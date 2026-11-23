-- Prove2me | solution 1 for KernelRank.coeff_prod_truncExpPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:13:44.83019+00:00
-- url     : https://prove2.me/submissions/f8ab30f8-d20d-4eef-9aed-3a64b801cc7f

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_coeff_truncExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {α : Type*} (S : Finset α) (k : ℕ) (u : α → ℂ)
    {q : ℕ} (hq : q ≤ k) :
    (∏ j ∈ S, truncExpPoly k (u j)).coeff q =
      (∑ j ∈ S, u j) ^ q / (q.factorial : ℂ) := by
  classical
  induction S using Finset.induction_on generalizing q with
  | empty =>
    cases q with
    | zero => simp
    | succ q => simp [zero_pow (Nat.succ_ne_zero q), coeff_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p =>
        (truncExpPoly k (u a)).coeff m * (∏ j ∈ S, truncExpPoly k (u j)).coeff p]
    have hterm : ∀ m ∈ Finset.range (q + 1),
        (truncExpPoly k (u a)).coeff m * (∏ j ∈ S, truncExpPoly k (u j)).coeff (q - m) =
          (u a ^ m * (∑ j ∈ S, u j) ^ (q - m) * (q.choose m : ℂ)) / (q.factorial : ℂ) := by
      intro m hm
      have hmq : m ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hmk : m ≤ k := by omega
      have hqmk : q - m ≤ k := by omega
      rw [coeff_truncExpPoly, ih hqmk]
      simp only [hmk, ↓reduceIte]
      have hchoose : (q.factorial : ℂ) =
          (q.choose m : ℂ) * (m.factorial : ℂ) * ((q - m).factorial : ℂ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hmq).symm
      have hf1 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
      have hf2 : ((q - m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q - m).factorial_ne_zero
      have hfq : (q.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
      field_simp
      rw [hchoose]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← _root_.add_pow]
end KernelRank
