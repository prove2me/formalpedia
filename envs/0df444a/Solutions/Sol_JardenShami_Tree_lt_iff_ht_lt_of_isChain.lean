-- Prove2me | solution 1 for JardenShami.Tree.lt_iff_ht_lt_of_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:06.469189+00:00
-- url     : https://prove2.me/submissions/46018f4d-563c-4861-89c3-74b7eee0b18d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Tree_ht_le_ht_of_le


set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {b : Set T} (hb : IsChain (· ≤ ·) b) {x y : T} (hx : x ∈ b)
    (hy : y ∈ b) : x < y ↔ ht x < ht y := by
  refine ⟨ht_lt_ht, fun h => ?_⟩
  rcases hb.total hx hy with h' | h'
  · exact h'.lt_of_ne fun e => h.ne (congrArg ht e)
  · exact absurd (ht_le_ht_of_le h') (not_le.2 h)
end JardenShami.Tree
