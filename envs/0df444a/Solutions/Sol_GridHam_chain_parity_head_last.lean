-- Prove2me | solution 1 for GridHam.chain_parity_head_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:46:25.315706+00:00
-- url     : https://prove2.me/submissions/b1ce15ac-0366-4b4e-a71d-321cbe329b93

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_GridHam_adjacent_parity_ne

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution :
    ∀ (l : List Coord) (a : Coord), chainAdjacent (a :: l) = true →
      ∀ (hne : (a :: l) ≠ []),
        parity ((a :: l).getLast hne) = (parity a + l.length) % 2 := by
  intro l
  induction l with
  | nil =>
    intro a hc hne
    have hgl : (a :: ([] : List Coord)).getLast hne = a := rfl
    rw [hgl]
    simp
    unfold parity
    omega
  | cons b rest ih =>
    intro a hc hne
    have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
      simpa [chainAdjacent] using hc
    simp at hc'
    obtain ⟨hab, hcl⟩ := hc'
    have hadj : Adjacent a b := by
      unfold adjacentB at hab
      by_contra hcon
      simp [hcon] at hab
    have hgetlast : (a :: b :: rest).getLast hne = (b :: rest).getLast (by simp) := rfl
    rw [hgetlast]
    have key := ih b hcl (by simp)
    have hpar : parity a ≠ parity b := adjacent_parity_ne hadj
    have ha2 : parity a < 2 := by unfold parity; omega
    have hbb2 : parity b < 2 := by unfold parity; omega
    have hlen : (b :: rest).length = rest.length + 1 := rfl
    omega
end GridHam
