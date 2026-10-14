-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T14:56:12.033988+00:00
-- url     : https://prove2.me/submissions/13912d4c-0343-464c-bf19-95edf982ad2d

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

theorem solution {nu : ℝ} (d : FixedData nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  classical
  -- A zero binomial product would make the entire scalar zero.
  have hprod : (∏ i : Fin d.m, (t.1.1 i).choose (beta d r i) *
      (t.1.1 i - beta d r i).choose (t.2.1 i).val : ℕ) ≠ 0 := by
    have hc : ((∏ i : Fin d.m, (t.1.1 i).choose (beta d r i) *
        (t.1.1 i - beta d r i).choose (t.2.1 i).val : ℕ) : ℂ) ≠ 0 := by
      intro hz
      apply ht
      simp [choiceScalar, RowTranslation.rowScalar, hz]
    exact_mod_cast hc
  have hcoord (i : Fin d.m) : beta d r i ≤ t.1.1 i := by
    have hterm := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
    have hchoose : (t.1.1 i).choose (beta d r i) ≠ 0 :=
      (Nat.mul_ne_zero_iff.mp hterm).1
    exact Nat.choose_ne_zero_iff.mp hchoose
  -- Each logarithmic weight is the real cast of a natural-number ceiling.
  have hweight (i : Fin d.m) : 0 ≤ fixedWeights d i := by
    unfold fixedWeights MatrixArithmetic.logWeights
    exact Nat.cast_nonneg _
  unfold rowWeight indexWeight MatrixTranslationBounds.weight
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcoord i) (hweight i)
