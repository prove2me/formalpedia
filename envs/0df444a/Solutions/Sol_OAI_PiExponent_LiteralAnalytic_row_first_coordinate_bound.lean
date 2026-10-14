-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.row_first_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:32:06.481259+00:00
-- url     : https://prove2.me/submissions/cdffdc30-0115-46a7-8f1c-3f6820cca224

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

theorem solution {nu : ℝ}
    (d : FixedData nu) (H : ℝ) (r : Row d H) :
    r.2.1 0 + 1 ≤ ⌊H / d.v0⌋₊ + 1 := by
  have hstrict : r.2.1 ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))) H := r.2.2
  have hr : r.2.1 ∈ realWeightedSimplex
      (InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    exact (Finset.mem_filter.mp hstrict).1
  have hpi : r.2.1 ∈ Fintype.piFinset (fun i =>
      Finset.range (⌊H / InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i⌋₊ + 1)) := by
    exact (Finset.mem_filter.mp hr).1
  have hzero := (Fintype.mem_piFinset.mp hpi) 0
  change r.2.1 0 ∈ Finset.range (⌊H / d.v0⌋₊ + 1) at hzero
  have hz : r.2.1 0 < ⌊H / d.v0⌋₊ + 1 := Finset.mem_range.mp hzero
  omega