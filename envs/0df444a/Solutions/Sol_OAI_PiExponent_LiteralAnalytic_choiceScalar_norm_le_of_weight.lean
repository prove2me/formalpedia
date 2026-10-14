-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choiceScalar_norm_le_of_weight
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T13:03:54.605175+00:00
-- url     : https://prove2.me/submissions/29b207e0-eaa5-44a4-a856-16cb77a371a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choice_center_error_exp
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choice_scalar_weight_inputs

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * d.translationError) := by
  rcases OAI.PiExponent.LiteralAnalytic.choice_scalar_weight_inputs d hH r t with
    ⟨hws, hv, hF, hw, ha, hk, hT, hTw⟩
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu := by
    apply add_nonneg _ hnu
    apply Real.log_nonneg
    have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
    linarith
  have hε : ∀ i, ‖(r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) := by
    intro i
    exact OAI.PiExponent.LiteralAnalytic.choice_center_error_exp d hnu r.1.val r.1.isLt.le i
  have hb := OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d)
    (Real.log (2 * (d.K : ℝ)) + nu) nu H d.wstar d.v0 d.F0
    hC hnu hws hv hF hw ha hk hT hTw hε
  simpa [choiceScalar, indexWeight, rowWeight, MatrixTranslationBounds.weight,
    AdmissibleParameters.translationError, add_assoc] using hb
