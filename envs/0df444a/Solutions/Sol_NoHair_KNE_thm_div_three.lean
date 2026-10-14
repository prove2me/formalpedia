-- Prove2me | solution 1 for NoHair.KNE.thm_div_three
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:27:55.823995+00:00
-- url     : https://prove2.me/submissions/d8549492-421f-41fc-8048-061c53c4b889

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Div4

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 3 3 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 3 ν σ) 3 y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) 3 ν σ) := by
  refine ⟨?_, ?_⟩
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG303 m a e y hy).1
    · exact (NoHair.KNE.dG313 m a e y hy).1
    · exact (NoHair.KNE.dG323 m a e y hy).1
    · exact (NoHair.KNE.dG333 m a e y hy).1
  · intro ν σ
    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG300 m a e y hy).2
    · exact (NoHair.KNE.dG301 m a e y hy).2
    · exact (NoHair.KNE.dG302 m a e y hy).2
    · exact (NoHair.KNE.dG303 m a e y hy).2
    · exact (NoHair.KNE.dG301 m a e y hy).2
    · exact (NoHair.KNE.dG311 m a e y hy).2
    · exact (NoHair.KNE.dG312 m a e y hy).2
    · exact (NoHair.KNE.dG313 m a e y hy).2
    · exact (NoHair.KNE.dG302 m a e y hy).2
    · exact (NoHair.KNE.dG312 m a e y hy).2
    · exact (NoHair.KNE.dG322 m a e y hy).2
    · exact (NoHair.KNE.dG323 m a e y hy).2
    · exact (NoHair.KNE.dG303 m a e y hy).2
    · exact (NoHair.KNE.dG313 m a e y hy).2
    · exact (NoHair.KNE.dG323 m a e y hy).2
    · exact (NoHair.KNE.dG333 m a e y hy).2
