-- Prove2me | solution 1 for KernelRank.natDegree_truncExpPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:14:31.147007+00:00
-- url     : https://prove2.me/submissions/ab99d1c1-bf90-4f77-bd6f-519c3f535c51

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
theorem _root_.solution (k : ℕ) (u : ℂ) : (truncExpPoly k u).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_truncExpPoly]
  simp [not_le.mpr hn]
end KernelRank
