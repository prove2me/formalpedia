-- Prove2me | solution 1 for Light.isDataStructure_of_program_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:27.569075+00:00
-- url     : https://prove2.me/submissions/e0bddb40-dfcb-4f0d-a438-c7939fcea85d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_isDataStructure_of_program
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
theorem _root_.solution {P : Program} {pPre pQ s k : ℕ} {extra : List ℤ}
    {dom : ThinPair → Prop} {Tp Sp Tq : ThinPair → ℝ} {A : ℝ}
    (h : ProgramIsDataStructure P pPre pQ s k extra dom (fun x => A * Tp x) (fun x => A * Sp x)
      fun x => A * Tq x)
    (h1 : ∀ x, dom x → 1 ≤ Tp x ∧ 1 ≤ Sp x ∧ 1 ≤ Tq x) :
    IsDataStructure (compileProgram P pPre false) (compileProgram P pQ false) cARG1 cARG2 cRESULT
      (slopeOf P false s k 2) extra dom (fun x => ((timeConst P false : ℝ) * (A + 1)) * Tp x)
      (fun x => ((timeConst P false : ℝ) * (A + 1)) * Sp x)
      (fun x => ((timeConst P false : ℝ) * (A + 1)) * Tq x) :=
  (isDataStructure_of_program h).mono le_rfl (fun _ hx => hx)
    (fun x hx => scaled_le (by positivity) (h1 x hx).1)
    (fun x hx => scaled_le (by positivity) (h1 x hx).2.1)
    fun x hx => scaled_le (by positivity) (h1 x hx).2.2
end Light
