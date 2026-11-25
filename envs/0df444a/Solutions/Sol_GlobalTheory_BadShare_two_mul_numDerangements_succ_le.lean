-- Prove2me | solution 1 for GlobalTheory.BadShare.two_mul_numDerangements_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:42.75098+00:00
-- url     : https://prove2.me/submissions/cb84b036-17e8-44ce-b7d6-dc3d2c2bf065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution (n : ℕ) :
    2 * numDerangements (n + 1) ≤ (n + 1).factorial := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [numDerangements]
  | more n h1 h2 =>
    have e : numDerangements (n + 2 + 1)
        = (n + 1 + 1) * (numDerangements (n + 1) + numDerangements (n + 1 + 1)) :=
      numDerangements_add_two (n + 1)
    have f1 : (n + 2 + 1).factorial = (n + 2 + 1) * (n + 1 + 1).factorial :=
      Nat.factorial_succ _
    have f2 : (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial :=
      Nat.factorial_succ _
    rw [e, f1]
    have := Nat.mul_le_mul_left (n + 1 + 1) (Nat.add_le_add h1 h2)
    nlinarith
end GlobalTheory.BadShare
