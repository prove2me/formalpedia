-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_scale_discount_sequence_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:41:43.839798+00:00
-- url     : https://prove2.me/submissions/6cc5b7c6-e01e-4e51-b291-33a53687874b

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
/-- Pointwise continuity of the source scale family at zero discount. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ 1) → Tendsto r atTop (nhds 0) →
      ∀ z : ℝ, Tendsto (fun n => W (r n) z) atTop (nhds (W 0 z)) := by
  intro ψ W hW r hr hlim z
  by_cases hz : 0 < z
  · let c : ℕ → ℝ := fun k => scaleConvolutionPower (W 0) k z
    have hc (k : ℕ) : 0 ≤ c k :=
      source_scale_power_nonnegative_all_real ψ W hW k z
    have hs : Summable c := by
      simpa only [one_pow, one_mul, c] using
        source_discount_series_summable_all_real ψ W hW 1 zero_le_one z
    have he (q : ℝ) (hq : 0 ≤ q) :
        W q z = ∑' k : ℕ, q ^ k * c k :=
      source_scale_discount_series_real_positive_x ψ W hW z q hz hq
    have ht : Tendsto (fun n => ∑' k : ℕ, (r n)^k * c k) atTop
        (nhds (∑' k : ℕ, (0 : ℝ)^k * c k)) := by
      apply tendsto_tsum_of_dominated_convergence hs
      · intro k
        exact (hlim.pow k).mul tendsto_const_nhds
      · filter_upwards with n k
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hr n).1.le _) (hc k))]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (pow_le_one₀ (hr n).1.le (hr n).2) (hc k)
    rw [← he 0 le_rfl] at ht
    exact ht.congr fun n => (he (r n) (hr n).1.le).symm
  · rcases eq_or_lt_of_le (le_of_not_gt hz) with he | hn
    · subst z
      exact tendsto_const_nhds.congr fun n =>
        (source_scale_origin_discount_invariant ψ W hW (r n) (hr n).1.le).symm
    · have he (n : ℕ) : W (r n) z = W 0 z :=
        ((hW (r n) (hr n).1.le).2.1 z hn).trans ((hW 0 le_rfl).2.1 z hn).symm
      exact tendsto_const_nhds.congr (fun n => (he n).symm)
