-- Prove2me | solution 1 for Kyprianou.Ch05.classicalRenewalTheorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:44:54.456402+00:00
-- url     : https://prove2.me/submissions/20b22b4e-3cdd-40c1-93af-552b39aaf18c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_nonlatticeIncrement
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_keyRenewalConvolution
import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_unrestrictedGrowth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
      ∀ h : Real → Real, DirectlyRiemannIntegrable h →
        Tendsto
          (fun x : Real =>
            ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
          atTop
          (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu))) ∧
     (Tendsto
       (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
       atTop (nhds (1 / mu))))
 := by
  exact ⟨
    Kyprianou.Ch05.classicalRenewalTheorem_nonlatticeIncrement F hSupport hFiniteMean hPositiveMean,
    Kyprianou.Ch05.classicalRenewalTheorem_keyRenewalConvolution F hSupport hFiniteMean hPositiveMean,
    Kyprianou.Ch05.classicalRenewalTheorem_unrestrictedGrowth F hSupport hFiniteMean hPositiveMean
  ⟩

