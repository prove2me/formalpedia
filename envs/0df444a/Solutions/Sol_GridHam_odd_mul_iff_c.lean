-- Prove2me | solution 1 for GridHam.odd_mul_iff_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:16:00.620645+00:00
-- url     : https://prove2.me/submissions/ce0b51c9-7553-4025-b9c0-fd72d1b29481

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

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
