-- Prove2me | solution 1 for KernelRank.coeff_revHassePoly_mul_prod_truncExpPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:08.411831+00:00
-- url     : https://prove2.me/submissions/23ff579f-53a5-413a-b5b8-cdfb34162d1a

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_coeff_prod_truncExpPoly
import Theorems.Thm_KernelRank_coeff_revHassePoly
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
theorem _root_.solution {d : ℕ} (P : ℂ[X]) (j₀ : Fin d) (u : Fin d → ℂ) :
    (revHassePoly P P.natDegree (u j₀) *
      ∏ j ∈ Finset.univ.erase j₀, truncExpPoly P.natDegree (u j)).coeff P.natDegree =
      P.eval (∑ j : Fin d, u j) := by
  let k := P.natDegree
  let rest : Finset (Fin d) := Finset.univ.erase j₀
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p =>
    (revHassePoly P k (u j₀)).coeff m * (∏ j ∈ rest, truncExpPoly k (u j)).coeff p]
  have hsum_u : u j₀ + ∑ j ∈ rest, u j = ∑ j : Fin d, u j :=
    Finset.add_sum_erase Finset.univ u (Finset.mem_univ j₀)
  let T := ∑ j ∈ rest, u j
  have hanti : ∑ m ∈ Finset.range (k + 1),
      (revHassePoly P k (u j₀)).coeff m * (∏ j ∈ rest, truncExpPoly k (u j)).coeff (k - m) =
      ∑ q ∈ Finset.range (k + 1), (hasseDeriv q P).eval (u j₀) * T ^ q := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqk : q ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hsub : k - (k - q) = q := by omega
    simp only [Nat.add_sub_cancel]
    rw [hsub, coeff_revHassePoly P k (u j₀) (Nat.sub_le k q), hsub,
      coeff_prod_truncExpPoly rest k u hqk]
    have hfq : (q.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
    dsimp [T]
    field_simp
  rw [hanti, ← hsum_u, add_comm (u j₀) T, ← taylor_eval,
    eval_eq_sum_range' (by rw [natDegree_taylor]; exact Nat.lt_succ_self k)]
  exact Finset.sum_congr rfl fun q _ => by rw [taylor_coeff]
end KernelRank
