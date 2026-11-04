-- Prove2me | solution 1 for Light.solves_of_programSolves_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:56.878633+00:00
-- url     : https://prove2.me/submissions/7c384664-9644-4699-bbd7-0d0c43c088c4

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_solves_of_programSolves
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono

section
open ThreeSumApsp.WordRam
namespace Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
section run
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
end run
private theorem scaled_le {C A T : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T) :
    C * (A * T) + C ≤ C * (A + 1) * T := by
  nlinarith [mul_le_mul_of_nonneg_left hT hC]
end Light
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
theorem _root_.solution {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool}
    {s k r : ℕ} {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} {A : ℝ}
    (h : ProgramSolves prob P p0 dec s k dom fun x => A * T x)
    (hr : ∀ x, (prob.params x).length ≤ r) (h1 : ∀ x, dom x → 1 ≤ T x) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => ((timeConst P dec : ℝ) * (A + 1)) * T x :=
  (solves_of_programSolves h hr).mono le_rfl (fun _ hx => hx) fun x hx =>
    scaled_le (by positivity) (h1 x hx)
end Light
