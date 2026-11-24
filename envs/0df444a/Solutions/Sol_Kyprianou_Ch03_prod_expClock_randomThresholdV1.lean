-- Prove2me | solution 1 for Kyprianou.Ch03.prod_expClock_randomThresholdV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:45:18.752857+00:00
-- url     : https://prove2.me/submissions/5ba70905-e3d3-4886-805d-94084e5ff24a

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_prod_expClock_sectionLIntegralV1
import Theorems.Thm_Kyprianou_Ch03_prod_expClock_survivalSectionV1
import Theorems.Thm_Kyprianou_Ch03_prod_expClock_discountMeasurableV1
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega OmegaE : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (q : ℝ) (hq : 0 < q) (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {z : OmegaE | t < e z}).toReal = Real.exp (-q * (t : ℝ))) :
    ((P.prod Q) {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)}).toReal =
      ∫ w, if tau w = ⊤ then (0 : ℝ)
        else Real.exp (-q * (((tau w).untopD (0 : NNReal) : NNReal) : ℝ)) ∂P := by
  rw [Kyprianou.Ch03.prod_expClock_sectionLIntegralV1 P Q tau htau e]
  have hh := Kyprianou.Ch03.prod_expClock_survivalSectionV1 Q q e hExponential
  simp_rw [hh]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Eventually.of_forall (fun w => by
      change 0 ≤ (if tau w = ⊤ then (0 : ℝ) else Real.exp (-q * (((tau w).untopD (0 : NNReal) : NNReal) : ℝ)))
      split <;> positivity)
  · exact (Kyprianou.Ch03.prod_expClock_discountMeasurableV1 tau htau q).aestronglyMeasurable
