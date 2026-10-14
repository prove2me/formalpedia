-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choice_center_error_exp
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T13:17:50.718044+00:00
-- url     : https://prove2.me/submissions/565fe5b9-c878-4593-87f6-21aa8f626f92

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

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    (j : ℕ) (hj : j ≤ d.K) (i : Fin d.m) :
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters (finiteNumerators d)
      (finiteDenominators d) i - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) := by
  let q : ℝ := (finiteDenominators d i : ℝ)
  let p : ℝ := (finiteNumerators d i : ℝ)
  have hq2 : 2 ≤ q := by
    change (2 : ℝ) ≤ (d.q i.val : ℝ)
    exact_mod_cast (d.approximations i.val).1
  have hqpos : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hq1nat : 1 ≤ d.q i.val := by
    have := (d.approximations i.val).1
    omega
  have hceillow : Real.log q ≤ fixedWeights d i := by
    dsimp [q, fixedWeights, finiteDenominators, MatrixArithmetic.logWeights]
    exact Nat.le_ceil _
  have hceilhigh : fixedWeights d i ≤ Real.log q + 1 := by
    dsimp [q, fixedWeights, finiteDenominators, MatrixArithmetic.logWeights]
    exact (Nat.ceil_lt_add_one (Real.log_nonneg (by exact_mod_cast hq1nat))).le
  have happrox : |Real.pi - p / q| ≤ q ^ (-nu) := by
    dsimp [p, q, finiteNumerators, finiteDenominators]
    exact (d.approximations i.val).2.2
  have hdecay : q ^ (-nu) ≤ Real.exp (nu - nu * fixedWeights d i) := by
    rw [Real.rpow_def_of_pos hqpos]
    apply Real.exp_le_exp.mpr
    have hmul : nu * fixedWeights d i ≤ nu * (Real.log q + 1) :=
      mul_le_mul_of_nonneg_left hceilhigh hnu
    nlinarith [hnu]
  have herror : ‖MatrixArithmetic.rationalCenters (finiteNumerators d)
      (finiteDenominators d) i - logarithmicPeriod‖ = 2 * |Real.pi - p / q| := by
    have hqC : (finiteDenominators d i : ℂ) ≠ 0 := by
      have hqNat : 0 < finiteDenominators d i := by
        dsimp [finiteDenominators]
        have := (d.approximations i.val).1
        omega
      exact_mod_cast hqNat.ne'
    have hform : MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d) i - logarithmicPeriod =
        (2 : ℂ) * Complex.I * (((p / q - Real.pi : ℝ) : ℂ)) := by
      dsimp [MatrixArithmetic.rationalCenters, logarithmicPeriod, p, q,
        finiteNumerators, finiteDenominators]
      push_cast
      field_simp
    rw [hform, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real]
    norm_num [Real.norm_eq_abs, abs_sub_comm]
  have hjreal : (j : ℝ) ≤ (d.K : ℝ) := by exact_mod_cast hj
  have hKpos : 0 < (d.K : ℝ) := by exact_mod_cast d.K_pos
  have hbound : (j : ℝ) * (2 * |Real.pi - p / q|) ≤
      (2 * (d.K : ℝ)) * Real.exp (nu - nu * fixedWeights d i) := by
    calc
      (j : ℝ) * (2 * |Real.pi - p / q|) ≤
          (d.K : ℝ) * (2 * q ^ (-nu)) := by
            gcongr
      _ = (2 * (d.K : ℝ)) * q ^ (-nu) := by ring
      _ ≤ (2 * (d.K : ℝ)) * Real.exp (nu - nu * fixedWeights d i) := by
            exact mul_le_mul_of_nonneg_left hdecay (by positivity)
  calc
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d) i - logarithmicPeriod)‖ =
      (j : ℝ) * (2 * |Real.pi - p / q|) := by
        rw [norm_mul, Complex.norm_natCast, herror]
    _ ≤ (2 * (d.K : ℝ)) * Real.exp (nu - nu * fixedWeights d i) := hbound
    _ = Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) := by
      calc
        _ = Real.exp (Real.log (2 * (d.K : ℝ))) * Real.exp (nu - nu * fixedWeights d i) := by
          rw [Real.exp_log (by positivity)]
        _ = Real.exp (Real.log (2 * (d.K : ℝ)) + (nu - nu * fixedWeights d i)) := by
          rw [← Real.exp_add]
        _ = _ := by congr 1 <;> ring
