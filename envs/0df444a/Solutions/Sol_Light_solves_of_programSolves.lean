-- Prove2me | solution 1 for Light.solves_of_programSolves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:12.0072+00:00
-- url     : https://prove2.me/submissions/d26c2142-d7e7-4a5a-a81a-30fde0408d82

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_fits_of_small
import Theorems.Thm_Light_ramSteps_le
import Theorems.Thm_Light_input_loadWords
import Theorems.Thm_Light_Compiler_Holds_output
import Theorems.Thm_Light_Compiler_compileProgram_correct
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans

section
open ThreeSumApsp.WordRam
namespace Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
private theorem ramSteps_le_of_le (P : Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * T + timeConst P dec :=
  (ramSteps_le P dec c).trans (by gcongr)
section run
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
end run
end Light
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
theorem _root_.solution {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool} {s k r : ℕ}
    {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} (h : ProgramSolves prob P p0 dec s k dom T)
    (hr : ∀ x, (prob.params x).length ≤ r) :
    Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => (timeConst P dec : ℝ) * T x + timeConst P dec := by
  intro x hx W hadm
  obtain ⟨lim, σ', c, h⟩ := h x hx
  have hfit := fits_of_small P dec h.small hadm (hr x) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct h.run hfit (input_loadWords W h.small.nonneg h.input_fits)
  refine ⟨_, _, cfg, ramSteps_le_of_le P dec h.time, hrun, ?_⟩
  rw [show output cfg (prob.input x).length = fun i => σ'.mem ((prob.input x).length + i) from
    funext (out.holds.output hfit _)]
  exact h.answer
end Light
