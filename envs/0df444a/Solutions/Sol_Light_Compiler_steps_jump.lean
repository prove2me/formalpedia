-- Prove2me | solution 1 for Light.Compiler.steps_jump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:06.21691+00:00
-- url     : https://prove2.me/submissions/60d3499d-dd24-4a6c-9b97-e30a0db3908c

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_steps_bltz
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}
namespace Light.Compiler
theorem _root_.solution {l : ℕ} (hcode : CodeAt code pos (.bltz cNEG l :: rest))
    (hneg : m cNEG = wd W (-1)) (hr : InRange W (-1)) : Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using steps_bltz hcode hneg hr
end Light.Compiler
