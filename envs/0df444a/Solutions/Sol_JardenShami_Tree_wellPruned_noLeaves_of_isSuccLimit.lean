-- Prove2me | solution 1 for JardenShami.Tree.wellPruned_noLeaves_of_isSuccLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:49.303369+00:00
-- url     : https://prove2.me/submissions/cd70ae2b-e0da-4ed1-be18-d2817de15dc5

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_ht_lt_height

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution (hT : WellPruned T)
    (hlim : Order.IsSuccLimit (height T)) : ∀ t : T, ¬ IsLeaf t := by
  intro t ht'
  obtain ⟨y, -, hy⟩ := hT.2 t (Order.succ (ht t)) (Order.lt_succ_of_not_isMax (not_isMax _))
    (hlim.succ_lt (ht_lt_height t))
  exact ht'.not_lt hy
end JardenShami.Tree
