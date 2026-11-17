-- Prove2me | solution 1 for Kyprianou.Ch07.heavyTailRuinAsymptoticAllParts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:25:16.576686+00:00
-- url     : https://prove2.me/submissions/eb59c9c6-f5dd-4046-a83d-07b312495ff5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_ruinIntegratedTailAsymptotic
import Theorems.Thm_Kyprianou_Ch07_ruinProbabilityRegularlyVarying
import Theorems.Thm_Kyprianou_Ch07_ruinOvershootPrejumpJointLimit
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (alpha : Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hSpectralPositive : Pi (Set.Iio 0) = 0)
    (hLeft : Kyprianou.Ch05.IsLeftLimitVersion P X Xleft)
    (hAlpha : 0 < alpha)
    (hMeanFinite : Integrable (X 1) P)
    (hMeanNegative : (∫ omega, X 1 omega ∂P) < 0)
    (hRegularTail : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (Pi (Set.Ioi x)).toReal) (-(alpha + 1))) :
    let lifetime : Omega → WithTop NNReal := fun _ => ⊤
    let ruin : Real → Set Omega := fun x =>
      {omega | Kyprianou.Ch05.PassageFinite X lifetime x omega}
    let overshoot : Real → Omega → Real := fun x omega =>
      Kyprianou.Ch05.passageOvershoot X lifetime x omega
    let prejump : Real → Omega → Real := fun x omega =>
      Xleft (Kyprianou.Ch05.passageFiniteTime X lifetime x omega) omega
    let integratedTail : Real → Real := fun x =>
      ∫ y : Real in Set.Ioi x, (Pi (Set.Ioi y)).toReal ∂volume
    ((Tendsto (fun x : Real =>
       (P (ruin x)).toReal / integratedTail x)
       atTop (nhds (1 / |∫ omega, X 1 omega ∂P|))) ∧
     Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (P (ruin x)).toReal) (-alpha) ∧
     (∀ u v : Real, 0 < u → 0 < v →
       Tendsto (fun x : Real =>
         (P {omega | omega ∈ ruin x ∧
             u < overshoot x omega / (x / alpha) ∧
             v < (-prejump x omega) / (x / alpha)}).toReal /
           (P (ruin x)).toReal)
         atTop (nhds ((1 + (u + v) / alpha) ^ (-alpha))))) := by
  dsimp only
  exact ⟨
    Kyprianou.Ch07.ruinIntegratedTailAsymptotic P X Xleft b sigma2 Pi alpha hX hTriplet hSpectralPositive hLeft hAlpha hMeanFinite hMeanNegative hRegularTail,
    Kyprianou.Ch07.ruinProbabilityRegularlyVarying P X Xleft b sigma2 Pi alpha hX hTriplet hSpectralPositive hLeft hAlpha hMeanFinite hMeanNegative hRegularTail,
    Kyprianou.Ch07.ruinOvershootPrejumpJointLimit P X Xleft b sigma2 Pi alpha hX hTriplet hSpectralPositive hLeft hAlpha hMeanFinite hMeanNegative hRegularTail⟩
