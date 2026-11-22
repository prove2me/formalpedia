-- Prove2me | solution 1 for GridHam.step_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:27.144855+00:00
-- url     : https://prove2.me/submissions/db7fe2af-ecde-46b9-b70b-b43c688f9e77

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
public import Theorems.Thm_GridHam_freeCol_exists
public import Theorems.Thm_GridHam_acc_iff
public import Theorems.Thm_GridHam_branchA
public import Theorems.Thm_GridHam_branchB
public import Theorems.Thm_GridHam_branchC
public import Theorems.Thm_GridHam_mem_primeShapes_of
public import Theorems.Thm_GridHam_prime_solvable
public import Theorems.Thm_GridHam_splitVertically_preserves_startLeft
public import Theorems.Thm_GridHam_stripLeft_preserves
public import Theorems.Thm_GridHam_stripRight_preserves


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (n : ℕ) (IH : SuffP n) (w h : ℕ) (s t : Coord)
    (hsz : w + h ≤ n + 1) (hwh : h ≤ w) (hle : s.1 ≤ t.1)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : HasHamPath w h s t := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < w ∧ sy < h := hs
  have ht' : tx < w ∧ ty < h := ht
  have hle' : sx ≤ tx := hle
  have hst' : ¬ (sx = tx ∧ sy = ty) := by
    rintro ⟨e1, e2⟩
    apply hst
    rw [e1, e2]
  have hA : AccA w h sx sy tx ty := (acc_iff w h (sx, sy) (tx, ty)).mp hacc
  by_cases hnp : NotPrime w h
  · have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
    by_cases hA2 : 2 ≤ sx
    · -- (A) strip the two leftmost columns
      obtain ⟨hsub, hfree⟩ := branchA w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA hA2
      apply stripLeft_preserves w h (sx, sy) (tx, ty) hA2 (by show 2 ≤ tx; omega)
        (freeCol_exists 2 h sx sy tx ty hfree)
      apply IH (w - 2) h (sx - 2, sy) (tx - 2, ty) (by omega)
        (show sx - 2 < w - 2 ∧ sy < h by omega) (show tx - 2 < w - 2 ∧ ty < h by omega)
      · intro e
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact hst' ⟨by omega, e2⟩
      · exact (acc_iff (w - 2) h (sx - 2, sy) (tx - 2, ty)).mpr hsub
    · by_cases hC : tx + 2 < w
      · -- (C) strip the two rightmost columns
        obtain ⟨hsub, hfree⟩ :=
          branchC w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) hC
        apply stripRight_preserves w h (sx, sy) (tx, ty) (by show sx + 2 < w; omega) hC
          (freeCol_exists (w - 3) h sx sy tx ty hfree)
        apply IH (w - 2) h (sx, sy) (tx, ty) (by omega)
          (show sx < w - 2 ∧ sy < h by omega) (show tx < w - 2 ∧ ty < h by omega) hst
        exact (acc_iff (w - 2) h (sx, sy) (tx, ty)).mpr hsub
      · -- (B) split after column 1 at row `rChoice sx sy h`
        have hB := branchB w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) (by omega)
        unfold BConcl at hB
        obtain ⟨hr, hs1, hq, haccL, haccR⟩ := hB
        have hleft : HasHamPath 2 h (sx, sy) (1, rChoice sx sy h) := by
          apply IH 2 h (sx, sy) (1, rChoice sx sy h) (by omega)
            (show sx < 2 ∧ sy < h by omega) (show 1 < 2 ∧ rChoice sx sy h < h by omega)
          · intro e
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            exact hs1 ⟨e1, e2⟩
          · exact (acc_iff 2 h (sx, sy) (1, rChoice sx sy h)).mpr haccL
        have hright : HasHamPath (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) := by
          apply IH (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) (by omega)
            (show 0 < w - 2 ∧ rChoice sx sy h < h by omega)
            (show tx - 2 < w - 2 ∧ ty < h by omega)
          · intro e
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            exact hq ⟨e1, e2⟩
          · exact (acc_iff (w - 2) h (0, rChoice sx sy h) (tx - 2, ty)).mpr haccR
        exact splitVertically_preserves_startLeft w h 1 (rChoice sx sy h) (sx, sy) (tx, ty)
          (by show sx < tx; omega) (by show sx ≤ 1; omega) (by show 1 < tx; omega)
          hr hleft hright
  · -- prime shape
    exact prime_solvable w h (sx, sy) (tx, ty)
      (mem_primeShapes_of w h (by omega) (by omega) hnp) hs ht hst hacc
end GridHam
