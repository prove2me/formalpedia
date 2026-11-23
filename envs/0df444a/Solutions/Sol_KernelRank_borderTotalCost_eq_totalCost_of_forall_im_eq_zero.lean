-- Prove2me | solution 1 for KernelRank.borderTotalCost_eq_totalCost_of_forall_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:41:59.367733+00:00
-- url     : https://prove2.me/submissions/54f5b873-a4d6-4d49-8742-ee374209af02

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution (d : ℕ) {cs : List Component}
    (him : ∀ c ∈ cs, c.rate.im = 0) :
    borderTotalCost d cs = totalCost cs := by
  unfold borderTotalCost totalCost
  congr 1
  refine List.map_congr_left fun c hc => ?_
  simp [Component.borderCost, Component.cost, Component.multiplicity, him c hc]
end KernelRank
