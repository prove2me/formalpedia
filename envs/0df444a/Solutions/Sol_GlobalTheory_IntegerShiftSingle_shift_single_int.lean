-- Prove2me | solution 1 for GlobalTheory.IntegerShiftSingle.shift_single_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:58.777826+00:00
-- url     : https://prove2.me/submissions/82540986-310d-4fe4-92f0-6d382c0f3061

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegerShiftSingle
universe u_1 u_2 u_3
namespace GlobalTheory.IntegerShiftSingle
theorem _root_.solution {ι : Type u_1} {R : Type u_2} {E : Type u_3} [DecidableEq ι] [Ring R]
    {F : (ι → R) → E} (h : ∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x)
    (i : ι) (k : ℤ) : ∀ x : ι → R, F (x + Pi.single i ((k : ℤ) : R)) = F x := by
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have : x + Pi.single i (((m : ℤ) + 1 : ℤ) : R) = (x + Pi.single i ((m : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [Int.cast_add, Int.cast_one, Pi.single_add, add_assoc]
    rw [this, h, ih]
  | pred m ih =>
    intro x
    have : x + Pi.single i ((-(m : ℤ) : ℤ) : R) = (x + Pi.single i ((-(m : ℤ) - 1 : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [add_assoc, ← Pi.single_add]
      congr 2
      push_cast
      first | rfl | ring | abel | simp
    rw [← ih x, this, h]
end GlobalTheory.IntegerShiftSingle
