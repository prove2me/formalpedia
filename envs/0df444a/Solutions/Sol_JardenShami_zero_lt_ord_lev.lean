-- Prove2me | solution 1 for JardenShami.zero_lt_ord_lev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:58.505793+00:00
-- url     : https://prove2.me/submissions/4ef56f50-0019-48d4-9569-bb8cbe8f220b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_lev_nonempty

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : IsKappaTree κ T) {α : Ordinal.{w}} (hα : α < κ.ord) :
    0 < (#(Lev T α)).ord := by
  rw [Cardinal.ord_pos, pos_iff_ne_zero, Cardinal.mk_ne_zero_iff]
  exact (lev_nonempty (hT.1 ▸ hα)).to_subtype
end JardenShami
