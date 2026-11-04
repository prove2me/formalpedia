-- Prove2me | solution 1 for Light.AnswersQueries.of_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:47.172338+00:00
-- url     : https://prove2.me/submissions/ab809053-ec1f-4725-8a16-c57a252dc73f

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_Meets_main

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
namespace AnswersQueries
theorem _root_.solution {lim : Limits} {P : Program} {pQ : ℕ} {x : ThinPair} {T : ℝ}
    {DS : (ℕ → ℤ) → Prop} {T' : ℕ} (hd : 0 < lim.depth) (hT : ((T' + 4 : ℕ) : ℝ) ≤ T)
    (h : ∀ μ, DS μ → ∀ I J : Fin x.N, Meets lim P pQ 1 [((I : ℕ) : ℤ), ((J : ℕ) : ℤ)] μ T'
      fun r μ' => r = (x.X * x.Y) I J ∧ DS μ') :
    AnswersQueries lim P pQ x T DS :=
  fun μ hμ I J => (h μ hμ I J).main hd hT
end AnswersQueries
end Light
