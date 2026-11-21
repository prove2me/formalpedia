-- Prove2me | solution 1 for JardenShami.exists_big_cone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:19.922401+00:00
-- url     : https://prove2.me/submissions/983930a3-83a6-4d73-a32a-6cde7894167b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
omit [IsTree T]
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}} (hκ : κ.IsRegular) {U L : Set T} (hU : κ ≤ #U)
    (hL : #L < κ) (hcov : ∀ s ∈ U, ∃ y ∈ L, y ≤ s) : ∃ y ∈ L, κ ≤ #(Set.Ici y) := by
  by_contra hc
  push Not at hc
  have hsub : U ⊆ ⋃ y : L, Set.Ici (y : T) := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := hcov s hs
    exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys⟩
  have := (Cardinal.mk_le_mk_of_subset hsub).trans Cardinal.mk_iUnion_le_sum_mk
  exact (hU.trans this).not_gt (Cardinal.sum_lt_of_isRegular hκ hL fun y => hc y y.2)
end JardenShami
