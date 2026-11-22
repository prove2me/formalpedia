-- Prove2me | solution 1 for GridHam.mul_mod_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:40.058066+00:00
-- url     : https://prove2.me/submissions/1250caf8-879b-4708-a974-893911580cde

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) : (w * h) % 2 = 1 ↔ w % 2 = 1 ∧ h % 2 = 1 := by
  rw [Nat.mul_mod]
  rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hw | hw <;>
    rcases (by omega : h % 2 = 0 ∨ h % 2 = 1) with hh | hh <;>
    simp [hw, hh]
end GridHam
