-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_scale_discount_unit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:42:04.349815+00:00
-- url     : https://prove2.me/submissions/52be6d73-c9eb-46cb-80cd-a99faf0e854c

import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_real_positive_x
import Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_summable_all_real
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Unit-discount scale function dominates lower discounts. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ z q : ℝ, 0 ≤ q → q ≤ 1 → W q z ≤ W 1 z := by
  intro ψ W hW z q hq hq1
  by_cases hz : 0 < z
  · rw [source_scale_discount_series_real_positive_x ψ W hW z q hz hq,
      source_scale_discount_series_real_positive_x ψ W hW z 1 hz zero_le_one]
    apply Summable.tsum_le_tsum
    · intro k
      apply mul_le_mul_of_nonneg_right _ (source_scale_power_nonnegative_all_real ψ W hW k z)
      simpa only [one_pow] using (pow_le_one₀ hq hq1 : q^k ≤ 1)
    · exact source_discount_series_summable_all_real ψ W hW q hq z
    · exact source_discount_series_summable_all_real ψ W hW 1 zero_le_one z
  · rcases eq_or_lt_of_le (le_of_not_gt hz) with he | hn
    · subst z
      rw [source_scale_origin_discount_invariant ψ W hW q hq,
        source_scale_origin_discount_invariant ψ W hW 1 zero_le_one]
    · rw [(hW q hq).2.1 z hn, (hW 1 zero_le_one).2.1 z hn]
