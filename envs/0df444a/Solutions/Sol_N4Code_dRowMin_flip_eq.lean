-- Prove2me | solution 1 for N4Code.dRowMin_flip_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:58.803729+00:00
-- url     : https://prove2.me/submissions/44971bd9-5663-4614-82d2-9862e6cdc50c

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_flip_zero
import Theorems.Thm_N4Code_min_image_sub_one
import Theorems.Thm_N4Code_min_image_add_one

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t : Fin n) (y : Word n) (hcol : C t = col0) :
    (y t = true → dRowMin C S hS (flipBit t y) = dRowMin C S hS y - 1) ∧
      (y t = false → dRowMin C S hS (flipBit t y) = dRowMin C S hS y + 1) := by
  constructor
  · intro hyt
    unfold dRowMin
    have hshift : (S.image (fun i => dRow C i (flipBit t y))).min'
          (hS.image (fun i => dRow C i (flipBit t y))) =
        (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) - 1 := by
      have hcong : S.image (fun i => dRow C i (flipBit t y)) =
          S.image (fun i => dRow C i y - 1) := by
        apply Finset.image_congr
        intro i _
        exact (dRow_flip_zero C t y hcol i).1 hyt
      calc
        (S.image (fun i => dRow C i (flipBit t y))).min'
              (hS.image (fun i => dRow C i (flipBit t y)))
            = (S.image (fun i => dRow C i y - 1)).min'
                (hS.image (fun i => dRow C i y - 1)) := by
                simp [hcong]
        _ = (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) - 1 :=
              min_image_sub_one hS
    rw [hshift]
  · intro hyt
    unfold dRowMin
    have hshift : (S.image (fun i => dRow C i (flipBit t y))).min'
          (hS.image (fun i => dRow C i (flipBit t y))) =
        (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) + 1 := by
      have hcong : S.image (fun i => dRow C i (flipBit t y)) =
          S.image (fun i => dRow C i y + 1) := by
        apply Finset.image_congr
        intro i _
        exact (dRow_flip_zero C t y hcol i).2 hyt
      calc
        (S.image (fun i => dRow C i (flipBit t y))).min'
              (hS.image (fun i => dRow C i (flipBit t y)))
            = (S.image (fun i => dRow C i y + 1)).min'
                (hS.image (fun i => dRow C i y + 1)) := by
                simp [hcong]
        _ = (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) + 1 :=
              min_image_add_one hS
    rw [hshift]
end N4Code
