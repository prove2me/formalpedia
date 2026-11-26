-- Prove2me | solution 1 for Kyprianou.Ch05.classicalRenewalTheoremV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:33:39.053825+00:00
-- url     : https://prove2.me/submissions/ec6fb230-4718-41c3-8c9d-0ac303c7ffbf

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_nonlatticeIncrement
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_keyRenewalConvolutionV2
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_unrestrictedGrowth
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05

/-- Theorem 5.1, pp. 112-113, all three renewal conclusions. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    ((NonLatticeMeasure F →
      ∀ y : Real, 0 < y →
        Tendsto
          (fun x : Real => (V (Set.Ioc x (x + y))).toReal)
          atTop (nhds (y / mu))) ∧
     (NonLatticeMeasure F →
      ∀ h : Real → Real, Measurable h → DirectlyRiemannIntegrable h →
        Tendsto
          (fun x : Real =>
            ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
          atTop
          (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu))) ∧
     (Tendsto
       (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
       atTop (nhds (1 / mu))))
 := by
  exact ⟨classicalRenewalTheorem_nonlatticeIncrement F hSupport hFiniteMean hPositiveMean, classicalRenewalTheorem_keyRenewalConvolutionV2 F hSupport hFiniteMean hPositiveMean, classicalRenewalTheorem_unrestrictedGrowth F hSupport hFiniteMean hPositiveMean⟩


