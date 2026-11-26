-- Prove2me | solution 1 for Kyprianou.Ch05.classicalRenewalTheorem_keyRenewalConvolutionV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:25:24.515384+00:00
-- url     : https://prove2.me/submissions/ee886957-ef28-4cdb-9e5b-77e4b2b10ec7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_nonlatticeIncrement
import Theorems.Thm_Kyprianou_Ch05_renewalLocalFiniteFromGrowth
import Theorems.Thm_Kyprianou_Ch05_blackwellUniformTruncatedIntervalBound
import Theorems.Thm_Kyprianou_Ch05_keyRenewalFromBlackwellMeasurableDRI
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Theorem 5.1(ii) corrected: measurable directly Riemann integrable key renewal theorem. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (NonLatticeMeasure F → ∀ h : Real → Real,
      Measurable h → DirectlyRiemannIntegrable h →
      Tendsto (fun x : Real => ∫ z in Set.Icc 0 x, h (x-z) ∂V)
        atTop (nhds ((∫ z in Set.Ici 0, h z ∂volume) / mu))) := by
  dsimp only
  intro hn h hm hd
  have hB := classicalRenewalTheorem_nonlatticeIncrement F hSupport hFiniteMean hPositiveMean hn
  have hf := renewalLocalFiniteFromGrowth F hSupport hFiniteMean hPositiveMean
  exact keyRenewalFromBlackwellMeasurableDRI (renewalMeasure F) _
    hPositiveMean hf hB
    (blackwellUniformTruncatedIntervalBound (renewalMeasure F) _ hPositiveMean hf hB)
    h hm hd
