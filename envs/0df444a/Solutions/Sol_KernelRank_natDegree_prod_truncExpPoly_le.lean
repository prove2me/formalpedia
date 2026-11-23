-- Prove2me | solution 1 for KernelRank.natDegree_prod_truncExpPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:17:17.87184+00:00
-- url     : https://prove2.me/submissions/4203f6f6-57b0-4bf1-b3f8-e286f070ab31

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_natDegree_truncExpPoly_le
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
theorem _root_.solution {α : Type*} (S : Finset α) (k : ℕ) (u : α → ℂ) :
    (∏ j ∈ S, truncExpPoly k (u j)).natDegree ≤ S.card * k := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_one_mul]
    exact (natDegree_mul_le).trans (by linarith [natDegree_truncExpPoly_le k (u a)])
end KernelRank
