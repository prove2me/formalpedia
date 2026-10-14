-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowWeight_sum_eq_actualMean
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T15:02:31.226928+00:00
-- url     : https://prove2.me/submissions/4689bed6-9e8f-4016-82a9-2768af2f0cef

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

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) =
      (actualRowCount d H : ℝ) * H * actualMean d H := by
  classical
  have hcount : 0 < actualRowCount d H := by
    rw [actualRowCount]
    have hK : 0 < d.K := Nat.zero_lt_of_lt d.K_pos
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨⟨0, hK⟩, ⟨0, ?_⟩⟩⟩
    simp [OAI.PiExponent.strictWeightedSimplex, OAI.PiExponent.realWeightedSimplex]
    exact ⟨le_of_lt hH, hH⟩
  have hsum : (∑ r : Row d H, rowWeight d r) =
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H := by
    simp [rowWeight, MatrixTranslationBounds.weight, beta, fixedWeights,
      InterpolationMatrix.exponentVector, MatrixArithmetic.rowWeightedSum]
    congr 1
    funext r
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  rw [show actualRowCount d H =
      Fintype.card (Row d H) by rfl]
  simp only [actualMean, MatrixArithmetic.meanRowWeight]
  have hden : (Fintype.card (Row d H) : ℝ) * H ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hcount)) (ne_of_gt hH)
  have hcard : (Fintype.card (Row d H) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcount)
  field_simp [hden, hcard]
  <;> ring
