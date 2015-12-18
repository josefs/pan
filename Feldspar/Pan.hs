{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}
module Feldspar.Pan where

import qualified Prelude as P
import Prelude (Int,foldr)

import Language.Syntactic

import Feldspar hiding (sugar,desugar,resugar)
import Feldspar.Vector.Shape
import Feldspar.Vector.MultiDim hiding (empty)
import Feldspar.Compiler

import Control.Applicative hiding (empty)

newtype Point = Point (Data Double, Data Double)

newtype Image a = Image { unImage :: (Point -> a) }

instance Functor Image where
  fmap f (Image g) = Image (f . g)

instance Applicative Image where
  pure a = Image (P.const a)
  Image f <*> Image a = Image (\p -> f p (a p))

type Region = Image (Data Bool)

even :: Integral a => Data a -> Data Bool
even i = i `rem` 2 == 0

vstrip :: Region
vstrip = Image (\(Point (x,y)) -> abs x <= (1/2))

checker :: Region
checker = Image (\(Point (x,y)) -> even (floor x + floor y :: Data IntN))

altRings :: Region
altRings = Image (\p -> even (floor (distO p) :: Data IntN))

distO :: Point -> Data Double
distO (Point (x,y)) = sqrt (x ** 2 + x ** 2)

newtype PolarPoint = PPoint (Data Double, Data Double)

fromPolar :: PolarPoint -> Point
fromPolar (PPoint (ρ,θ)) = Point (ρ * cos θ, ρ * sin θ)

toPolar :: Point -> PolarPoint
toPolar p@(Point (x,y)) = PPoint (distO p, atan2 y x)

type Frac = Data Double

wavDist :: Image Frac
wavDist = Image (\p -> 1 + cos (π * distO p) / 2)

-- BGRA
newtype Colour = Colour (Frac, Frac, Frac, Frac)

instance Syntactic Colour where
  type Domain Colour = FeldDomain
  type Internal Colour = (Double,Double,Double,Double)
  desugar (Colour cs) = desugar cs
  sugar = Colour . sugar


invisible :: Colour
invisible = Colour (0,0,0,0)

red   = Colour (0,0,1,1)
green = Colour (0,1,0,1)
blue  = Colour (1,0,0,1)
white = Colour (1,1,1,1)
black = Colour (0,0,0,1)
yellow = Colour (0,1,1,1)

interpolateC :: Frac -> Colour -> Colour -> Colour
interpolateC w (Colour (b1,g1,r1,a1)) (Colour (b2,g2,r2,a2))
  = Colour (h b1 b2, h g1 g2, h r1 r2, h a1 a2)
  where h x1 x2 = w * x1 + (1 - w) * x2

lighten :: Frac -> Colour -> Colour
lighten w c = interpolateC w c white

darken :: Frac -> Colour -> Colour
darken w c = interpolateC w c black

biInterpolateC :: Colour -> Colour -> Colour -> Colour -> (Frac,Frac) -> Colour
biInterpolateC ll lr ul ur (dx,dy) =
  interpolateC dy (interpolateC dx ll lr) (interpolateC dx ul ur)

biInterpolateBRBW = biInterpolateC black red blue white

overC :: Colour -> Colour -> Colour
Colour (b1,g1,r1,a1) `overC` Colour (b2,g2,r2,a2)
  = Colour (h b1 b2,h g1 g2,h r1 r2,h a1 a2)
  where
    h x1 x2 = x1 + (1 - a1) * x2

type ImageC = Image Colour

over :: ImageC -> ImageC -> ImageC
Image top `over` Image bot = Image (\p -> top p `overC` bot p)

cond :: Syntax a => Image (Data Bool) -> Image a -> Image a -> Image a
cond = liftA3 (\a b c -> a ? b $ c)

interpolate :: Image Frac -> ImageC -> ImageC -> ImageC
interpolate = liftA3 interpolateC

empty, whiteI, blackI, redI, greenI, blueI :: ImageC
empty  = Image (const invisible)
whiteI = Image (const white)
blackI = Image (const black)
redI   = Image (const red)
greenI = Image (const green)
blueI  = Image (const blue)
yellowI = Image (const yellow)

ybRings = interpolate wavDist blueI yellowI

type Transform = Point -> Point
type TransformP = PolarPoint -> PolarPoint

newtype Vector = Vector (Data Double, Data Double)

translateP :: Vector -> Transform
translateP (Vector (dx,dy)) (Point (x,y)) = Point (x+dx,y+dy)

scaleP :: Vector -> Transform
scaleP (Vector (sx,sy)) (Point (x,y)) = Point (sx * x, sy * y)

uscaleP :: Data Double -> Transform
uscaleP s = scaleP (Vector (s,s))

rotateP :: Data Double -> Transform
rotateP θ (Point (x,y)) =
  Point (x * cos θ - y * sin θ, y * cos θ + x * sin θ)

type Filter a = Image a -> Image a

translate, scale :: Vector -> Filter a
uscale, rotate   :: Data Double -> Filter a

translate (Vector (dx,dy)) (Image f) = Image (f . translateP (Vector (-dx,-dy)))
scale     (Vector (sx,sy)) (Image f) = Image (f . scaleP (Vector (1/sx,1/sy)))
uscale    s                (Image f) = Image (f . uscaleP (1/s))
rotate    θ                (Image f) = Image (f . rotateP (-θ))

swirlP :: Data Double -> Transform
swirlP r p = rotateP (distO p * 2 * π / r) p

swirl :: Data Double -> Filter a
swirl r (Image f) = Image (f . swirlP (-r))

type FilterC = Filter Colour

xPos :: Region
xPos = Image (\(Point (x,_)) -> x > 0)

udisk :: Region
udisk = Image (\p -> distO p < 1)

universeR, emptyR :: Region
compR             :: Region -> Region
(⋂),(⋃),xorR,(\\) :: Region -> Region -> Region
(⊗)               :: Region -> Region -> Region

universeR = Image (const true)
emptyR    = Image (const false)

compR     = liftA not

(⋂)       = liftA2 (&&)
(⋃)       = liftA2 (||)
xorR      = liftA2 (/=)
r \\ r'   = r ⋂ compR r'
(⊗)       = xorR

annulus :: Frac -> Region
annulus inner = udisk \\ uscale inner udisk

radReg :: Data IntN -> Region
radReg n = Image (test . toPolar)
 where test (PPoint (_,θ)) = even (floor (θ * i2f n / π) :: Data IntN)

wedgeAnnulus :: Data Double -> Data IntN -> Region
wedgeAnnulus inner n = annulus inner ⋂ radReg n

shiftXor :: Data Double -> Filter (Data Bool)
shiftXor r reg = reg' r ⊗ reg' (-r)
  where reg' d = translate (Vector (d,0)) reg

xorgon :: IntN -> Data Double -> Region
xorgon n r = xorRs (fmap (rf . value) [0 .. n-1])
  where rf i = translate (pointToVector (fromPolar (PPoint (r,a)))) altRings
          where a = i2f i * 2 * π / i2f (value n)

pointToVector :: Point -> Vector
pointToVector (Point (x,y)) = Vector (x,y)

xorRs :: [Region] -> Region
xorRs = foldr xorR emptyR

polarChecker n = altRings ⊗ radReg n

crop :: Region -> FilterC
crop reg im = cond reg im empty

-- Alternate version
-- swirlP r = polarXf (\(ρ,θ) -> (ρ,θ + ρ * 2 * π / r))

polarXf :: TransformP -> Transform
polarXf xf = fromPolar . xf . toPolar

radInvertP :: Transform
radInvertP = polarXf (\(PPoint (ρ,θ)) -> (PPoint (1/ρ,θ)))

radInvert :: Image a -> Image a
radInvert (Image im) = Image (im . radInvertP)

rippleRadP :: Data IntN -> Data Double -> Transform
rippleRadP n s = polarXf $ \(PPoint (ρ,θ)) ->
                  PPoint (ρ * (1 + s * sin (i2f n * θ)), θ)

rippleRad :: Data IntN -> Data Double -> Image a -> Image a
rippleRad n s (Image im) = Image (im . rippleRadP n (-s))

cropRad :: Data Double -> FilterC
cropRad r = crop (uscale r udisk)

circleLimit :: Data Double -> FilterC
circleLimit radius (Image im) = cropRad radius (Image (im . polarXf xf))
  where xf (PPoint (ρ,θ)) = PPoint (radius * ρ / (radius - ρ), θ)

biInterpolate :: ((Data IntN,Data IntN) -> Colour) -> ImageC
biInterpolate sub = Image $ \(Point (x,y)) ->
  let i = floor x; wx = x - i2f i
      j = floor y; wy = y - i2f j
  in biInterpolateC (sub (i,j))   (sub (i+1,j))
                    (sub (i,j+1)) (sub (i+1,j+1))
                    (wx,wy)

reconstruct :: Pully vec DIM2 => vec DIM2 Colour -> ImageC
reconstruct vec = 
  translate (Vector  (- i2f w / 2, - i2f h / 2))
       (crop (inBounds (i2n w) (i2n h)) (biInterpolate sub))
  where sub (x,y) = vec !: (Z :. i2n y :. i2n x)
        [w,h] = toList (extent vec)

inBounds :: Data IntN -> Data IntN -> Region
inBounds w h = Image (\(Point (x,y)) ->
                       0 <= x && x <= i2f (w - 1) &&
                       0 <= y && y <= i2f (h - 1))

-- | Samples the unit rectangle (0,1).
sample :: Data Length -> Data Length -> ImageC -> Pull DIM2 Colour
sample w h (Image f) =
  indexed (\(Z :. x :. y) -> f (Point (i2f x / i2f w,i2f y / i2f h))) (Z :. w :. h)

-- | Sample a colour
sampleC :: Data WordN -> Colour -> [Data WordN]
sampleC w (Colour (b,g,r,a)) = [s b, s g, s r, s a]
  where s v = f2i (i2f w * v)

sampleImage :: Data WordN -> Data Length -> Data Length ->
               ImageC -> Push DIM3 (Data WordN) 
sampleImage depth w h im = flattenList (fmap (sampleC depth) (sample w h im))

-- Clastic
{-
xfun1 = Image (\(Point (x,y)) -> sin (x + sin (y + sin x)) -
                                 sin (y + sin (x + sin y)) )

xfun2 = Image (\(Point (x,y)) -> floor (sin (x + sin (y + sin x))) -
                                 floor (sin (y + sin (x + sin y))) )

imag1 = interpol rGold rBlue linear (.) sscaled 0.1 xfun1
-}
