-- Prove2me | solution 1 for HajnalSzemeredi.card_classes_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:35.618455+00:00
-- url     : https://prove2.me/submissions/76a5842e-1bd3-47e3-a9ba-a6328fb923bf

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_HajnalSzemeredi_Final
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} [Fintype V]
namespace HajnalSzemeredi
theorem _root_.solution {W : Type*} [Fintype W] {p : ℕ} (f : V ⊕ Fin p → W) (i : W) :
    (univ.filter fun w => f w = i).card =
      (univ.filter fun v => f (.inl v) = i).card + (univ.filter fun j => f (.inr j) = i).card := by
  simp only [card_filter, Fintype.sum_sum_type]
end HajnalSzemeredi
