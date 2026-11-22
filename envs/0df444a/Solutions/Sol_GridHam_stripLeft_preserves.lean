-- Prove2me | solution 1 for GridHam.stripLeft_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:43:05.24993+00:00
-- url     : https://prove2.me/submissions/0fa7fe07-bc9f-4cd9-b2cf-be958affa6e5

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_stripRight_preserves
public import Theorems.Thm_GridHam_hasHamPath_bounds
public import Theorems.Thm_GridHam_hasHamPath_reflect

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : 2 ≤ s.1) (ht : 2 ≤ t.1)
    (hfree : ∃ y, y < height ∧ (2, y) ≠ s ∧ (2, y) ≠ t)
    (h : HasHamPath (width - 2) height (s.1 - 2, s.2) (t.1 - 2, t.2)) :
    HasHamPath width height s t := by
  obtain ⟨y, hy, hys, hyt⟩ := hfree
  have hb := hasHamPath_bounds h
  unfold InBounds at hb
  dsimp only at hb
  obtain ⟨⟨hsx, hsy⟩, ⟨htx, hty⟩⟩ := hb
  have hR := hasHamPath_reflect h
  have es : reflectX (width - 2) (s.1 - 2, s.2) = reflectX width s := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  have et : reflectX (width - 2) (t.1 - 2, t.2) = reflectX width t := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  rw [es, et] at hR
  have hS := stripRight_preserves width height (reflectX width s) (reflectX width t)
    (by unfold reflectX; dsimp only; omega) (by unfold reflectX; dsimp only; omega)
    ⟨y, hy,
      (by
        intro heq
        apply hys
        unfold reflectX at heq
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp only at h1 h2
        ext
        · show 2 = s.1
          omega
        · show y = s.2
          exact h2),
      (by
        intro heq
        apply hyt
        unfold reflectX at heq
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp only at h1 h2
        ext
        · show 2 = t.1
          omega
        · show y = t.2
          exact h2)⟩
    hR
  have hB := hasHamPath_reflect hS
  have ss : reflectX width (reflectX width s) = s := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  have tt : reflectX width (reflectX width t) = t := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  rw [ss, tt] at hB
  exact hB
end GridHam
