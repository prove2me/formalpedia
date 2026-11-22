-- Prove2me | solution 1 for GridHam.cnt1_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:16:16.031853+00:00
-- url     : https://prove2.me/submissions/2552fe50-8569-4039-be7e-f137c4a74188

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_GridHam_adjacent_parity_ne
public import Theorems.Thm_GridHam_cnt1_cons

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l : List Coord) (a : Coord), chainAdjacent (a :: l) = true →
    cnt1 (a :: l) = (l.length + 1 + parity a) / 2 := by
  intro l
  induction l with
  | nil =>
    intro a _
    rw [cnt1_cons, show cnt1 [] = 0 from rfl, List.length_nil]
    have ha2 : parity a < 2 := by unfold parity; omega
    split_ifs <;> omega
  | cons b l' ih =>
    intro a hch
    have hc' : (adjacentB a b && chainAdjacent (b :: l')) = true := by
      simpa [chainAdjacent] using hch
    simp at hc'
    obtain ⟨hab, hcl⟩ := hc'
    have hadj : Adjacent a b := by
      unfold adjacentB at hab
      by_contra hcon
      simp [hcon] at hab
    have hne := adjacent_parity_ne hadj
    have ha2 : parity a < 2 := by unfold parity; omega
    have hb2 : parity b < 2 := by unfold parity; omega
    rw [cnt1_cons, ih b hcl, List.length_cons]
    split_ifs <;> omega
end GridHam
