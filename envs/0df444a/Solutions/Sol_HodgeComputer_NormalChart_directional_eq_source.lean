-- Prove2me | solution 1 for HodgeComputer.NormalChart.directional_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T01:45:19.599326+00:00
-- url     : https://prove2.me/submissions/bf209cad-9cbe-4ba4-ab58-d1bdc2f4389d

import Definitions.Def_HodgeComputerNormalChart
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open HodgeComputer HodgeComputer.NormalChart MvPolynomial
open scoped BigOperators

theorem solution (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    directional F (numerator F A S W) = A * (denominator F S) := by
  simp only [directional, Fin.sum_univ_succ, numerator, Fin.cases_zero, Fin.cases_succ,
    denominator]
  have he (j : Fin 5) : pderiv j.succ F * (normal F * W j) =
      normal F * (pderiv j.succ F * W j) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold normal
  ring
