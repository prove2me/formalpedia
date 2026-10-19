-- Prove2me | solution 2 for OAI.PiExponent.MatrixTranslationBounds.actual_error_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T14:29:19.811528+00:00
-- url     : https://prove2.me/submissions/c0b66c08-eebc-4348-ab5e-b8aa32ae89eb

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have hqpos : (0 : ℝ) < (q i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hq i))
  have hcenter :
      MatrixArithmetic.rationalCenters p q i - logarithmicPeriod =
        (2 * Complex.I) * (((p i : ℝ) / (q i : ℝ) - Real.pi : ℝ) : ℂ) := by
    unfold MatrixArithmetic.rationalCenters logarithmicPeriod
    push_cast
    ring
  have hnorm :
      ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ =
        2 * (j : ℝ) * |Real.pi - (p i : ℝ) / (q i : ℝ)| := by
    calc
      _ = (j : ℝ) * ‖MatrixArithmetic.rationalCenters p q i - logarithmicPeriod‖ := by
        rw [norm_mul]
        simp only [Complex.norm_natCast]
      _ = (j : ℝ) * (2 * |Real.pi - (p i : ℝ) / (q i : ℝ)|) := by
        congr 1
        calc
          _ = ‖2 * Complex.I‖ *
              ‖(((p i : ℝ) / (q i : ℝ) - Real.pi : ℝ) : ℂ)‖ := by
                rw [hcenter, norm_mul]
          _ = 2 * |(p i : ℝ) / (q i : ℝ) - Real.pi| := by
                simp only [norm_mul, Complex.norm_I, Complex.norm_real,
                  Real.norm_eq_abs]
                norm_num
          _ = 2 * |Real.pi - (p i : ℝ) / (q i : ℝ)| := by
                rw [abs_sub_comm]
      _ = _ := by ring
  have hjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
  have hqpow : 0 ≤ (q i : ℝ) ^ (-ν) := Real.rpow_nonneg hqpos.le _
  have hlog : 0 ≤ Real.log (q i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq i)
  have hceil : (⌈Real.log (q i : ℝ)⌉₊ : ℝ) -
      Real.log (q i : ℝ) < 1 := by
    have hc := Nat.ceil_lt_add_one hlog
    linarith
  have hpow : (q i : ℝ) ^ (-ν) ≤
      Real.exp ν * Real.exp (-ν * (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) := by
    rw [Real.rpow_def_of_pos hqpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ =
        2 * (j : ℝ) * |Real.pi - (p i : ℝ) / (q i : ℝ)| := hnorm
    _ ≤ 2 * (K : ℝ) * (q i : ℝ) ^ (-ν) := by
      calc
        2 * (j : ℝ) * |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤
            2 * (j : ℝ) * (q i : ℝ) ^ (-ν) :=
          mul_le_mul_of_nonneg_left (happrox i) (by positivity)
        _ ≤ 2 * (K : ℝ) * (q i : ℝ) ^ (-ν) :=
          mul_le_mul_of_nonneg_right (by nlinarith [hjR]) hqpow
    _ ≤ 2 * (K : ℝ) *
        (Real.exp ν * Real.exp (-ν * (⌈Real.log (q i : ℝ)⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp ((Real.log (2 * (K : ℝ)) + ν) -
          ν * MatrixArithmetic.logWeights q i) := by
      have hKpos : (0 : ℝ) < 2 * (K : ℝ) := by
        exact_mod_cast (by omega : 0 < 2 * K)
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
      simp [MatrixArithmetic.logWeights, mul_comm, mul_left_comm, mul_assoc]
