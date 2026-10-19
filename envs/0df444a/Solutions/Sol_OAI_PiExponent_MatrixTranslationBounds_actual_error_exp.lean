-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.actual_error_exp
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:51:52.580833+00:00
-- url     : https://prove2.me/submissions/ac978214-3a6d-464f-81f6-5ab9f09a27cc

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
import Definitions.Def_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_scaled_rational_center_error
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rounded_log_weight_majorant

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixArithmetic

theorem solution {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (ν : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |Real.pi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν)) :
    ∀ i, ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) -
        ν * MatrixArithmetic.logWeights q i) := by
  intro i
  have hcenter :=
    OAI.PiExponent.MatrixTranslationBounds.scaled_rational_center_error
      p q j i (hq i)
  have happrox' :
      (2 * (j : ℝ)) * |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤
        (2 * (j : ℝ)) * ((q i : ℝ) ^ (-ν)) := by
    exact mul_le_mul_of_nonneg_left (happrox i) (by positivity)
  have hmajor :=
    OAI.PiExponent.MatrixTranslationBounds.rounded_log_weight_majorant
      K j ν (q i) hK hj hν (hq i)
  calc
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖
        ≤ (2 * (j : ℝ)) * |Real.pi - (p i : ℝ) / (q i : ℝ)| := hcenter
    _ ≤ (2 * (j : ℝ)) * ((q i : ℝ) ^ (-ν)) := happrox'
    _ ≤ Real.exp ((Real.log (2 * (K : ℝ)) + ν) -
        ν * MatrixArithmetic.logWeights q i) := by
      simpa [MatrixArithmetic.logWeights] using hmajor