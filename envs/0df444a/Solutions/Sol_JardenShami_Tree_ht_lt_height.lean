-- Prove2me | solution 1 for JardenShami.Tree.ht_lt_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:26.770316+00:00
-- url     : https://prove2.me/submissions/b3515bce-edce-4176-a3e7-98ad82b23992

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
theorem _root_.solution (t : T) : ht t < height T := by
  have hne : {α | Lev T α = ∅}.Nonempty := by
    obtain ⟨b, hb⟩ := Ordinal.bddAbove_of_small (s := Set.range (ht : T → Ordinal.{w}))
    refine ⟨Order.succ b, Set.eq_empty_of_forall_notMem fun x hx => ?_⟩
    exact (Order.lt_succ_iff.2 (hb ⟨x, rfl⟩)).ne hx
  rw [height, ← Order.succ_le_iff]
  refine le_csInf hne fun α hα => Order.succ_le_of_lt ?_
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with h | h
  · obtain ⟨s, -, hs⟩ := exists_lt_ht_eq h
    exact (Set.eq_empty_iff_forall_notMem.1 hα) s hs
  · exact (Set.eq_empty_iff_forall_notMem.1 hα) t h.symm
end JardenShami.Tree
