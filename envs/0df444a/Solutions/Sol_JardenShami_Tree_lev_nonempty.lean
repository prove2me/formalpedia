-- Prove2me | solution 1 for JardenShami.Tree.lev_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:27.586967+00:00
-- url     : https://prove2.me/submissions/4014fd27-14ca-44e4-957c-e5a39b1aa5ae

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {α : Ordinal.{w}} (h : α < height T) : (Lev T α).Nonempty := by
  by_contra hc
  exact (csInf_le' (s := {β : Ordinal.{w} | Lev T β = ∅})
    (Set.not_nonempty_iff_eq_empty.1 hc)).not_gt h
end JardenShami.Tree
