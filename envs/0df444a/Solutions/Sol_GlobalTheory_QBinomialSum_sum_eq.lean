-- Prove2me | solution 1 for GlobalTheory.QBinomialSum.sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:32.143766+00:00
-- url     : https://prove2.me/submissions/10b44e43-8b48-4f82-87a0-953f29419c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Theorems.Thm_GlobalTheory_QBinomialSum_prod_succ_succ
import Theorems.Thm_GlobalTheory_QBinomialSum_den_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.QBinomialSum
namespace GlobalTheory.QBinomialSum
theorem _root_.solution (x : ℂ) (hx : x ≠ 0) (h1 : ∀ k : ℕ, x ^ (k + 1) - 1 ≠ 0) (n : ℕ) :
    ∑ a ∈ Finset.range n,
      (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c : ℕ → ℂ := fun a => (∏ i ∈ Finset.range a, (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range a, (x ^ a - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) with hc
    have key : ∀ a, (∏ i ∈ Finset.range (a + 1), (x ^ (n + 1) - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) =
        (∏ i ∈ Finset.range (a + 1), (x ^ n - x ^ i)) /
        (∏ i ∈ Finset.range (a + 1), (x ^ (a + 1) - x ^ i)) *
        (∏ i ∈ Finset.range a, (1 - x ^ (i + 1))) + (c a - c (a + 1)) := by
      intro a
      simp only [hc]
      rw [prod_succ_succ x n a, prod_succ_succ x a a,
        Finset.prod_range_succ (fun i => x ^ n - x ^ i),
        Finset.prod_range_succ (fun i => 1 - x ^ (i + 1))]
      have hd := den_ne x hx h1 a
      have h2 := h1 a
      have h3 := pow_ne_zero a hx
      generalize ∏ i ∈ Finset.range a, (x ^ a - x ^ i) = D at *
      generalize ∏ i ∈ Finset.range a, (x ^ n - x ^ i) = P at *
      generalize ∏ i ∈ Finset.range a, (1 - x ^ (i + 1)) = F at *
      field_simp
      ring
    have hz : ∏ i ∈ Finset.range (n + 1), (x ^ n - x ^ i) = 0 :=
      Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _)
    simp only [key]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih, hz]
    have h0 : c 0 = 1 := by simp [hc]
    have hn : c (n + 1) = 0 := by simp only [hc, hz]; simp
    rw [h0, hn]
    push_cast
    simp
end GlobalTheory.QBinomialSum
