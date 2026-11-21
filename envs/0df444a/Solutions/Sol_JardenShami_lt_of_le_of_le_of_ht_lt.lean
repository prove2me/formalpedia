-- Prove2me | solution 1 for JardenShami.lt_of_le_of_le_of_ht_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:19.252683+00:00
-- url     : https://prove2.me/submissions/86d9cf50-16af-4e5f-a239-ec8c2966246b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_ht_le_ht_of_le
import Theorems.Thm_JardenShami_le_total_of_le

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {x y z : T} (hx : x ≤ z) (hy : y ≤ z) (h : ht x < ht y) :
    x < y := by
  rcases le_total_of_le hx hy with h' | h'
  · exact h'.lt_of_ne fun hxy => h.ne (congrArg ht hxy)
  · exact absurd (ht_le_ht_of_le h') (not_le.2 h)
end JardenShami
