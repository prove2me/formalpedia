-- Prove2me | solution 1 for GlobalTheory.PerronPsi.sum_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:58.387896+00:00
-- url     : https://prove2.me/submissions/dbb66782-2313-45e3-a6d9-5b4568661649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Theorems.Thm_GlobalTheory_PerronPsi_harm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 2 + B * (2 * (1 + Real.log N)) := by
  have hz1 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((N - (N + 1 + x) : ℕ) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [show N - (N + 1 + x) = 0 by omega]
      simp
    rw [h0, add_zero]
    have := Finset.sum_range_reflect (fun k : ℕ => 1 / (k : ℝ)) (N + 1)
    simpa using this
  have hz2 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((x - (N + 1) : ℕ) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show x - (N + 1) = 0 by omega]
      simp
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    rw [show N + 1 + x - (N + 1) = x by omega]
  have hsplit : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n
      = (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N then (1 : ℝ) else 0))
        + (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N + 1 then (1 : ℝ) else 0))
        + B * (∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ)
          + ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ)) := by
    simp only [w, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  rw [hsplit, hz1, hz2]
  simp only [Finset.sum_ite_eq', Finset.mem_range, show N < N + 1 + (N + 1) by omega,
    show N + 1 < N + 1 + (N + 1) by omega, if_true]
  have h := harm N
  have h2 := mul_le_mul_of_nonneg_left
    (show ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) + ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ)
      ≤ 2 * (1 + Real.log N) by linarith) hB
  linarith
end GlobalTheory.PerronPsi
