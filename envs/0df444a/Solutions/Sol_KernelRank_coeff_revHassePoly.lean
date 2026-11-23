-- Prove2me | solution 1 for KernelRank.coeff_revHassePoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:35:22.832106+00:00
-- url     : https://prove2.me/submissions/920d34a9-9a38-4661-b9b9-de1f5ade21d6

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
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
theorem _root_.solution (P : ℂ[X]) (k : ℕ) (u : ℂ) {n : ℕ} (hn : n ≤ k) :
    (revHassePoly P k u).coeff n =
      ((k - n).factorial : ℂ) * (hasseDeriv (k - n) P).eval u := by
  simp only [revHassePoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single (k - n)]
  · have hkn : k - (k - n) = n := by omega
    simp [hkn]
  · intro q hq hne
    have hq' : q ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have : n ≠ k - q := by omega
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h
end KernelRank
