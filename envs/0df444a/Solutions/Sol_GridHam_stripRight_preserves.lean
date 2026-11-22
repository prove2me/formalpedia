-- Prove2me | solution 1 for GridHam.stripRight_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:39:26.189435+00:00
-- url     : https://prove2.me/submissions/aaefbc9b-3ca1-4f32-9ce4-53e3d721ff39

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_GridHam_exists_col_edge
public import Theorems.Thm_GridHam_chainAdjacent_suffix
public import Theorems.Thm_GridHam_validPath_reverse
public import Theorems.Thm_GridHam_extend_right_up

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : s.1 + 2 < width) (_ht : t.1 + 2 < width)
    (hfree : ∃ y, y < height ∧ (width - 3, y) ≠ s ∧ (width - 3, y) ≠ t)
    (h : HasHamPath (width - 2) height s t) :
    HasHamPath width height s t := by
  obtain ⟨y0, hy0, hys, hyt⟩ := hfree
  obtain ⟨p, hv⟩ := h
  have hv0 := hv
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv0
  have hw1 : 1 ≤ width - 2 := by omega
  have hvmem : (width - 3, y0) ∈ p :=
    hcov _ ((mem_allCoords _ _ _).mpr ⟨by dsimp only; omega, hy0⟩)
  have hhd : p.head? ≠ some (width - 3, y0) := by
    intro h
    rw [hhead] at h
    exact hys (Option.some.inj h).symm
  have hlst : p.getLast? ≠ some (width - 3, y0) := by
    intro h
    rw [hlast] at h
    exact hyt (Option.some.inj h).symm
  have hbound : ∀ u ∈ p, u.1 ≤ width - 3 := by
    intro u hu
    have hu' := hin u hu
    unfold InBounds at hu'
    omega
  obtain ⟨l1, a, b, l2, hp, ha, hb⟩ :=
    exists_col_edge (width - 3) p hch hnd hbound _ hvmem rfl hhd hlst
  have hc2 : chainAdjacent (a :: b :: l2) = true :=
    chainAdjacent_suffix l1 _ (by rw [← hp]; exact hch)
  have hc' : (adjacentB a b && chainAdjacent (b :: l2)) = true := by
    simpa [chainAdjacent] using hc2
  simp at hc'
  obtain ⟨hab, _⟩ := hc'
  have hadj : Adjacent a b := by
    unfold adjacentB at hab
    by_contra hcon
    simp [hcon] at hab
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, byy⟩ := b
  dsimp only at ha hb
  unfold Adjacent at hadj
  dsimp only at hadj
  have hax : ax = width - 2 - 1 := by omega
  have hbx : bx = width - 2 - 1 := by omega
  rw [hax, hbx] at hp
  have e : width - 2 + 2 = width := by omega
  rcases (show byy = ay + 1 ∨ ay = byy + 1 by omega) with hup | hdown
  · rw [hup] at hp
    have hv2 : ValidPath (width - 2) height s t
        (l1 ++ (width - 2 - 1, ay) :: (width - 2 - 1, ay + 1) :: l2) := by
      rw [← hp]
      exact hv
    have hN := extend_right_up (width - 2) height s t l1 l2 ay hw1 hv2
    rw [e] at hN
    exact ⟨_, hN⟩
  · rw [hdown] at hp
    have hrev : p.reverse =
        l2.reverse ++ (width - 2 - 1, byy) :: (width - 2 - 1, byy + 1) :: l1.reverse := by
      rw [hp]
      simp
    have hv2 : ValidPath (width - 2) height t s
        (l2.reverse ++ (width - 2 - 1, byy) :: (width - 2 - 1, byy + 1) :: l1.reverse) := by
      rw [← hrev]
      exact validPath_reverse hv
    have hN := extend_right_up (width - 2) height t s l2.reverse l1.reverse byy hw1 hv2
    rw [e] at hN
    exact ⟨_, validPath_reverse hN⟩
end GridHam
