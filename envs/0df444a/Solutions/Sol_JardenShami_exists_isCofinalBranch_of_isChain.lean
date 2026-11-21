-- Prove2me | solution 1 for JardenShami.exists_isCofinalBranch_of_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:55.762471+00:00
-- url     : https://prove2.me/submissions/a5d840a4-3acd-4a03-b421-6052abf62a95

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_Tree_isCofinalBranch_iff
import Theorems.Thm_JardenShami_Tree_mk_le_of_isChain


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}} {T : Type w} [PartialOrder T]
    [IsTree T] (hT : IsKappaTree κ T) {c : Set T} (hc : IsChain (· ≤ ·) c) (hcκ : κ ≤ #c) :
    ∃ b : Set T, IsCofinalBranch b := by
  obtain ⟨M, hM, hcM⟩ := hc.exists_maxChain
  refine ⟨M, (isCofinalBranch_iff hT.1).2 ⟨hM, le_antisymm (mk_le_of_isChain hT.1 hM.1) ?_⟩⟩
  exact hcκ.trans (Cardinal.mk_le_mk_of_subset hcM)
end JardenShami
