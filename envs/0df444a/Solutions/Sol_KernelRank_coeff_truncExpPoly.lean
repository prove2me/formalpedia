-- Prove2me | solution 1 for KernelRank.coeff_truncExpPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:12:04.535801+00:00
-- url     : https://prove2.me/submissions/4b693ce0-a48e-4bc5-8b86-102f84d4abba

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
theorem _root_.solution (k : ℕ) (u : ℂ) (q : ℕ) :
    (truncExpPoly k u).coeff q = if q ≤ k then u ^ q / (q.factorial : ℂ) else 0 := by
  simp only [truncExpPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp
end KernelRank
