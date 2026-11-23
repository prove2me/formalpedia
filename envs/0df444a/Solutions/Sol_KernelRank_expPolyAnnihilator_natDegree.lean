-- Prove2me | solution 1 for KernelRank.expPolyAnnihilator_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:09:56.724837+00:00
-- url     : https://prove2.me/submissions/6c73959d-7862-456c-8eed-56bf9050ebcf

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
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
theorem _root_.solution {ι : Type*} [Fintype ι] (P : ι → ℂ[X]) (rate : ι → ℂ) :
    (expPolyAnnihilator P rate).natDegree = ∑ i, ((P i).natDegree + 1) := by
  rw [expPolyAnnihilator, natDegree_prod_of_monic _ _
    (fun i _ => (monic_X_sub_C (rate i)).pow _)]
  simp
end KernelRank
