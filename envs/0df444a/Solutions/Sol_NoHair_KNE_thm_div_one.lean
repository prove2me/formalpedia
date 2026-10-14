-- Prove2me | solution 1 for NoHair.KNE.thm_div_one
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:25:57.695696+00:00
-- url     : https://prove2.me/submissions/2d6e5530-6657-4f60-af50-aefa36eeb1b4

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Div1
import Definitions.Def_NoHair_KerrNewmanEinstein_Div2

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 0 0 σ) y) ∧
    (∀ σ, DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 1 1 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 1 ν σ) 1 y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) 1 ν σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact NoHair.KNE.dG000 m a e y hy
    · exact NoHair.KNE.dG001 m a e y hy
    · exact NoHair.KNE.dG002 m a e y hy
    · exact NoHair.KNE.dG003 m a e y hy
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG101 m a e y hy).1
    · exact (NoHair.KNE.dG111 m a e y hy).1
    · exact (NoHair.KNE.dG112 m a e y hy).1
    · exact (NoHair.KNE.dG113 m a e y hy).1
  · intro ν σ
    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG100 m a e y hy).2
    · exact (NoHair.KNE.dG101 m a e y hy).2
    · exact (NoHair.KNE.dG102 m a e y hy).2
    · exact (NoHair.KNE.dG103 m a e y hy).2
    · exact (NoHair.KNE.dG101 m a e y hy).2
    · exact (NoHair.KNE.dG111 m a e y hy).2
    · exact (NoHair.KNE.dG112 m a e y hy).2
    · exact (NoHair.KNE.dG113 m a e y hy).2
    · exact (NoHair.KNE.dG102 m a e y hy).2
    · exact (NoHair.KNE.dG112 m a e y hy).2
    · exact (NoHair.KNE.dG122 m a e y hy).2
    · exact (NoHair.KNE.dG123 m a e y hy).2
    · exact (NoHair.KNE.dG103 m a e y hy).2
    · exact (NoHair.KNE.dG113 m a e y hy).2
    · exact (NoHair.KNE.dG123 m a e y hy).2
    · exact (NoHair.KNE.dG133 m a e y hy).2
