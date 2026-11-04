-- Prove2me | solution 1 for Light.Compiler.Holds.output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:55.60576+00:00
-- url     : https://prove2.me/submissions/cb974d65-427c-4c37-9981-96954ef043f1

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_Compiler_Fits_inRange
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c
import Theorems.Thm_ThreeSumApsp_WordRam_toInt_wd


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
namespace Light
namespace Compiler.Holds
theorem _root_.solution {c : ℤ → BitVec W} (h : Holds W lim μ c) {N Q : ℕ}
    (hfit : Fits W lim N Q) (off i : ℕ) : WordRam.output c off i = μ (off + i) := by
  rw [WordRam.output, ← Nat.cast_add, h.rep]
  exact toInt_wd (hfit.inRange (h.bounded _))
end Compiler.Holds
end Light
