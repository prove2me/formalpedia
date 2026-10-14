-- Prove2me | solution 1 for NoHair.KNE.thm_div_two
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:26:49.214625+00:00
-- url     : https://prove2.me/submissions/6ea33bad-53aa-435d-9fcb-244d5ed2396a

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Div3

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 2 2 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 2 ν σ) 2 y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) 2 ν σ) := by
  refine ⟨?_, ?_⟩
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG202 m a e y hy).1
    · exact (NoHair.KNE.dG212 m a e y hy).1
    · exact (NoHair.KNE.dG222 m a e y hy).1
    · exact (NoHair.KNE.dG223 m a e y hy).1
  · intro ν σ
    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG200 m a e y hy).2
    · exact (NoHair.KNE.dG201 m a e y hy).2
    · exact (NoHair.KNE.dG202 m a e y hy).2
    · exact (NoHair.KNE.dG203 m a e y hy).2
    · exact (NoHair.KNE.dG201 m a e y hy).2
    · exact (NoHair.KNE.dG211 m a e y hy).2
    · exact (NoHair.KNE.dG212 m a e y hy).2
    · exact (NoHair.KNE.dG213 m a e y hy).2
    · exact (NoHair.KNE.dG202 m a e y hy).2
    · exact (NoHair.KNE.dG212 m a e y hy).2
    · exact (NoHair.KNE.dG222 m a e y hy).2
    · exact (NoHair.KNE.dG223 m a e y hy).2
    · exact (NoHair.KNE.dG203 m a e y hy).2
    · exact (NoHair.KNE.dG213 m a e y hy).2
    · exact (NoHair.KNE.dG223 m a e y hy).2
    · exact (NoHair.KNE.dG233 m a e y hy).2
