-- Prove2me | solution 1 for GridHam.chain_parity_alternates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:43:47.039008+00:00
-- url     : https://prove2.me/submissions/4e1f2f3d-8ffe-44f1-bb0e-eaadc74f5c44

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_GridHam_adjacent_parity_ne

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (p : List Coord) (hc : chainAdjacent p = true) :
    ∀ i (hi : i < p.length) (h0 : 0 < p.length),
      parity (p.get ⟨i, hi⟩) = (parity (p.get ⟨0, h0⟩) + i) % 2 := by
  induction p with
  | nil => intro i hi h0; simp at h0
  | cons a l ih =>
    intro i hi h0
    cases i with
    | zero => simp; unfold parity; omega
    | succ n =>
      cases l with
      | nil => simp at hi
      | cons b rest =>
        have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
          simpa [chainAdjacent] using hc
        simp at hc'
        obtain ⟨hab, hcl⟩ := hc'
        have hadj : Adjacent a b := by
          unfold adjacentB at hab
          by_contra hcon
          simp [hcon] at hab
        have hln : n < (b :: rest).length := by
          have hlen : (a :: b :: rest).length = (b :: rest).length + 1 := by simp
          omega
        have key := ih hcl n hln (by omega)
        have hpar : parity a ≠ parity b := adjacent_parity_ne hadj
        have ha2 : parity a < 2 := by unfold parity; omega
        have hbb2 : parity b < 2 := by unfold parity; omega
        have goalLHS : (a :: b :: rest).get ⟨n + 1, hi⟩ = (b :: rest).get ⟨n, hln⟩ := by simp
        have goalRHS0 : (a :: b :: rest).get ⟨0, h0⟩ = a := by simp
        have hb0 : (b :: rest).get ⟨0, (by omega : 0 < (b :: rest).length)⟩ = b := by simp
        rw [goalLHS, goalRHS0]
        simp only [hb0] at key
        omega
end GridHam
