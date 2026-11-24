-- Prove2me | solution 1 for Kyprianou.Ch02.levyGridCharDefectLinearV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:19:17.056259+00:00
-- url     : https://prove2.me/submissions/0703072e-6b11-430e-8161-a0163badefd4

import Theorems.Thm_ProbabilityTheory_leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp
import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (z : ℂ) (C : ℝ)
    (h : ∀ n : ℕ, ((n : ℝ)+1) *
      (1 - Complex.exp (((((n : ℝ)+1)⁻¹) : ℂ) * z)).re ≤ C) :
    -z.re ≤ C := by
  let t : ℕ → ℝ := fun n => ((n : ℝ)+1)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have htne : ∀ n, t n ≠ 0 := by
    intro n
    dsimp [t]
    positivity
  have htp : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
    rw [nhdsWithin, tendsto_inf]
    refine ⟨ht, ?_⟩
    exact tendsto_principal.mpr (Eventually.of_forall htne)
  have hl := (ProbabilityTheory.leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp z).comp htp
  have h' : ∀ n : ℕ, (t n)⁻¹ * (1 - exp (↑(t n) * z)).re ≤ C := by
    intro n
    simpa [t] using h n
  simpa using le_of_tendsto hl (Eventually.of_forall h')
