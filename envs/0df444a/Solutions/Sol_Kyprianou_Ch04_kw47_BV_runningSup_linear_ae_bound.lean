-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_BV_runningSup_linear_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:00:28.074308+00:00
-- url     : https://prove2.me/submissions/104fe3fc-19cb-45be-b7cc-e8801a777eb1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- BV Lévy paths have the running supremum bounded by the
positive part of their linear drift, uniformly up to each horizon. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (T : NNReal) :
    ∀ᵐ w ∂P, runningSup L T w ≤ max 0 ((T : Real) * L.drift) := by
  have hX := bv_actual_levy_drift_upper_ae_all_times L hBV
  filter_upwards [hX] with w hw
  rw [Kyprianou.Ch04.kw47_runningSup_raw_eq L]
  apply csSup_le
  · exact ⟨L.X 0 w, ⟨0, by simp, rfl⟩⟩
  · rintro x ⟨s, hsT, rfl⟩
    have hST : (s : Real) ≤ (T : Real) := by exact_mod_cast hsT
    have hs0 : 0 ≤ (s : Real) := NNReal.coe_nonneg _
    have hLinear : (s : Real) * L.drift ≤
        max 0 ((T : Real) * L.drift) := by
      by_cases hd : 0 ≤ L.drift
      · have hm := mul_le_mul_of_nonneg_right hST hd
        exact hm.trans (le_max_right _ _)
      · have hm : (s : Real) * L.drift ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_not_ge hd)
        exact hm.trans (le_max_left _ _)
    exact (hw s).trans hLinear
