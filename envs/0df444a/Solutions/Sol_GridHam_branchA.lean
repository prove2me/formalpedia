-- Prove2me | solution 1 for GridHam.branchA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:54.64943+00:00
-- url     : https://prove2.me/submissions/2ab0fbef-d2c2-428a-8a41-e868f9e04c31

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
public import Theorems.Thm_GridHam_accA_big
public import Theorems.Thm_GridHam_accA_h1
public import Theorems.Thm_GridHam_accA_h2
public import Theorems.Thm_GridHam_accA_h3
public import Theorems.Thm_GridHam_branchA_small

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hA : 2 ≤ sx) :
    AccA (w - 2) h (sx - 2) sy (tx - 2) ty ∧ FreeCol 2 h sx sy tx ty := by
  have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
  by_cases hw6 : w < 6
  · exact branchA_small w (List.mem_range.mpr hw6) hw4 h (List.mem_range.mpr (by omega)) hnp
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
      hst hle hacc hA
  · unfold FreeCol
    rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3 ∨ 4 ≤ h) with hh | hh | hh | hh
    · subst hh
      rw [accA_h1 w sx sy tx ty (by omega)] at hacc
      unfold CCA EndsA at hacc
      exfalso
      omega
    · subst hh
      rw [accA_h2 w sx sy tx ty (by omega)] at hacc
      rw [accA_h2 (w - 2) (sx - 2) sy (tx - 2) ty (by omega)]
      unfold CCA F2A cornerA at hacc ⊢
      constructor
      · omega
      · omega
    · subst hh
      rw [accA_h3 w sx sy tx ty (by omega)] at hacc
      rw [accA_h3 (w - 2) (sx - 2) sy (tx - 2) ty (by omega)]
      unfold CCA G3 at hacc ⊢
      constructor
      · omega
      · omega
    · rw [accA_big w h sx sy tx ty (by omega) hh] at hacc
      rw [accA_big (w - 2) h (sx - 2) sy (tx - 2) ty (by omega) hh]
      unfold CCA at hacc ⊢
      constructor
      · omega
      · omega
end GridHam
