-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choiceScalar_weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:00:33.732542+00:00
-- url     : https://prove2.me/submissions/80879f2b-75ab-4b98-8c3a-8dc9d0850b92

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
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ∑ i : Fin d.m, fixedWeights d i *
        ((t.1.1 i : ℝ) - (beta d r i : ℝ)) =
      indexWeight d t.1 - rowWeight d r := by
  simp only [indexWeight, rowWeight, MatrixTranslationBounds.weight]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring