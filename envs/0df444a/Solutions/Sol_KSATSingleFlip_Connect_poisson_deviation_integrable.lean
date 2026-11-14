-- Prove2me | solution 1 for KSATSingleFlip.Connect.poisson_deviation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:35.31854+00:00
-- url     : https://prove2.me/submissions/4103d6ba-9e82-4a78-bb76-e02e26847673

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem solution (r : ℝ≥0) :
    Integrable (fun k : ℕ => |(k:ℝ) - (r:ℝ)|) (poissonMeasure r) ∧
    (∫ k : ℕ, |(k:ℝ) - (r:ℝ)| ∂(poissonMeasure r)) ≤ Real.sqrt (r:ℝ) := by
  let X : ℕ → ℝ := fun k => (k:ℝ) - (r:ℝ)
  have hv := AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum r
  have hs : Summable (fun k : ℕ => (Real.exp (-(r:ℝ)) * (r:ℝ)^k / (k.factorial:ℝ)) * (X k)^2) := by
    convert hv.summable using 1
    ext k
    simp only [X, poissonMeasure_real_singleton]
    ring
  have hi : Integrable (fun k : ℕ => (X k)^2) (poissonMeasure r) := by
    apply integrable_poissonMeasure_iff.mpr
    convert hs using 1
    ext k
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X k))]
  have hm : MemLp X 2 (poissonMeasure r) := by
    apply (memLp_two_iff_integrable_sq ?_).2
    · exact hi
    · fun_prop
  have hmoment : (∫ k, (X k)^2 ∂(poissonMeasure r)) = (r:ℝ) := by
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    convert hv.tsum_eq using 1
    congr 1
    funext k
    simp only [X, poissonMeasure_real_singleton]
    ring
  refine ⟨?_, ?_⟩
  · exact hm.abs.integrable (by norm_num)
  have hn : 0 ≤ ∫ k, |X k| ∂(poissonMeasure r) := integral_nonneg (fun k => abs_nonneg _)
  have hv' := variance_nonneg (fun k => |X k|) (poissonMeasure r)
  change 0 ≤ variance |X| (poissonMeasure r) at hv'
  rw [variance_eq_sub hm.abs] at hv'
  change 0 ≤ (∫ k, |X k|^2 ∂(poissonMeasure r)) - (∫ k, |X k| ∂(poissonMeasure r))^2 at hv'
  simp only [sq_abs, hmoment] at hv'
  apply (Real.le_sqrt hn r.coe_nonneg).2
  linarith
