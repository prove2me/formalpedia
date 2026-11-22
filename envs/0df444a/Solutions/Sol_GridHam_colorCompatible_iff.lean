-- Prove2me | solution 1 for GridHam.colorCompatible_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:22:48.893641+00:00
-- url     : https://prove2.me/submissions/1a50301a-47e6-4d72-94f2-427ed5cb156a

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
public import Theorems.Thm_GridHam_mul_mod_two_eq_one

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) :
    ColorCompatible w h (sx, sy) (tx, ty) ↔
      ((w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
        (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)) := by
  unfold ColorCompatible parity
  split_ifs with hodd
  · rw [mul_mod_two_eq_one] at hodd
    try dsimp only
    constructor <;> intro h <;> omega
  · rw [mul_mod_two_eq_one] at hodd
    try dsimp only
    constructor <;> intro h <;> omega
end GridHam
