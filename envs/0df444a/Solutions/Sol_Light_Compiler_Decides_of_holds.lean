-- Prove2me | solution 1 for Light.Compiler.Decides.of_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:27.643374+00:00
-- url     : https://prove2.me/submissions/58ffc6f6-870b-4ba6-a8c1-3c9d82d97132

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}
namespace Light.Compiler
namespace Decides
theorem _root_.solution {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ :=
  let ⟨m', n, le, A, run, _⟩ := h
  ⟨m', n, le, A, run hp⟩
end Decides
end Light.Compiler
