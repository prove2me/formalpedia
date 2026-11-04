-- Prove2me | solution 1 for Light.ramSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:58.296479+00:00
-- url     : https://prove2.me/submissions/ae2f031b-297c-4c33-a952-fe933f5fd9f9

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
theorem _root_.solution (P : Program) (dec : Bool) (c : ℕ) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * (c : ℝ) + timeConst P dec := by
  have hstart : startCost P dec ≤ timeConst P dec := by unfold timeConst; omega
  have hsim : stepsPerStep (dispPos P dec) ≤ timeConst P dec := by unfold timeConst; omega
  have : ramSteps P dec c ≤ timeConst P dec * c + timeConst P dec :=
    (Nat.add_comm _ _).trans_le (Nat.add_le_add (Nat.mul_le_mul_right c hsim) hstart)
  exact_mod_cast this
end Light
