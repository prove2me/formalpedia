-- Prove2me | solution 1 for KernelRank.natDegree_revHassePoly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:12:31.84479+00:00
-- url     : https://prove2.me/submissions/bd1e7aa3-ef4a-4ac7-bc20-ca954b49c5d9

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
theorem _root_.solution (P : ℂ[X]) (k : ℕ) (u : ℂ) :
    (revHassePoly P k u).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  simp only [revHassePoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  refine Finset.sum_eq_zero fun q hq => ?_
  have : n ≠ k - q := by omega
  simp [this]
end KernelRank
