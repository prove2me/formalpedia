-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actual_minor_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T09:11:13.592833+00:00
-- url     : https://prove2.me/submissions/6d00e7db-a24e-4f14-9d03-d32b8a385592

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_entry_row_choice_expansion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det =
      ∑ f : ChoiceFamily d H, (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det := by
  classical
  let v (r : Row d H) (t : RowChoice d H r) : Row d H → ℂ :=
    fun c => choiceScalar d r t *
      PowerSeries.coeff (r.2.1 0 - t.2.2)
        ((MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
          ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff t.1.1)
  have hM : actualMinor d H selection = fun r => ∑ t, v r t := by
    ext r c
    simpa [v, Finset.sum_apply, actualMinor, actualMatrix,
      MatrixArithmetic.selectedMinor, Matrix.submatrix] using
      (actual_entry_row_choice_expansion d r (selection c))
  rw [hM]
  change Matrix.detRowAlternating.toMultilinearMap (fun r => ∑ t, v r t) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact Matrix.det_mul_column (fun r => choiceScalar d r (f r))
    (choiceMatrix d selection f)
