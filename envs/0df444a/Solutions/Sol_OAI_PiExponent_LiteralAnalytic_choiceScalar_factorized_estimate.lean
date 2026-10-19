-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choiceScalar_factorized_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:01:36.249101+00:00
-- url     : https://prove2.me/submissions/09d69970-2117-48f6-b731-db32af242184

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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceScalar_norm_le_majorant
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant_le

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp (H * d.translationError) *
      Real.exp (-nu * ∑ i : Fin d.m, fixedWeights d i *
        ((t.1.1 i : ℝ) - (beta d r i : ℝ))) := by
  calc
    ‖choiceScalar d r t‖ ≤ choiceScalarMajorant d r t :=
      OAI.PiExponent.LiteralAnalytic.choiceScalar_norm_le_majorant d hnu r t
    _ ≤ Real.exp (H * d.translationError) *
        Real.exp (-nu * ∑ i : Fin d.m, fixedWeights d i *
          ((t.1.1 i : ℝ) - (beta d r i : ℝ))) :=
      OAI.PiExponent.LiteralAnalytic.choiceScalarMajorant_le d hnu r t