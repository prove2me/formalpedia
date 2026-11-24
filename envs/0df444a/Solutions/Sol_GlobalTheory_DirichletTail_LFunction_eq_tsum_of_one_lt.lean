-- Prove2me | solution 1 for GlobalTheory.DirichletTail.LFunction_eq_tsum_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:10.324132+00:00
-- url     : https://prove2.me/submissions/6a69a678-d1d5-46e9-b7ac-4fbc17bfae2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_tendsto_rpow_neg
import Theorems.Thm_GlobalTheory_DirichletTail_abel
import Theorems.Thm_GlobalTheory_DirichletTail_summable_term
import Theorems.Thm_GlobalTheory_DirichletTail_norm_boundary_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : LFunction χ s = ∑' n, term χ n s := by
  have hs0 : 0 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hL : HasSum (fun n : ℕ ↦ χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s))
      (LSeries (χ ·) s) := by
    have h := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h
    have e : (fun n : ℕ ↦ χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s)) =
        fun n ↦ LSeries.term (fun x ↦ χ x) s (n + 1) := by
      funext n
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    rw [e]
    exact h
  have hB : Tendsto (fun N : ℕ ↦ (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) *
      ((N + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N ↦ norm_boundary_le χ hχ s N) ?_
    simpa using (tendsto_rpow_neg hs0 0).const_mul (q : ℝ)
  have h3 := ((summable_term χ hχ hs0).hasSum.tendsto_sum_nat).add hB
  rw [add_zero] at h3
  exact tendsto_nhds_unique (hL.tendsto_sum_nat.congr fun N ↦ abel χ s N) h3
end GlobalTheory.DirichletTail
