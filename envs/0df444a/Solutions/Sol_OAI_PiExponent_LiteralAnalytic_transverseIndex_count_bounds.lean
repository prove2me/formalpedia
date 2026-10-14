-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.transverseIndex_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:19:58.828497+00:00
-- url     : https://prove2.me/submissions/5b894c3b-42d7-46a2-a4b4-44a0a96777e5

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_transverseIndices_coordinate_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_row_first_coordinate_bound
import Theorems.Thm_OAI_PiExponent_finiteFinset_box_card
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
    Fintype.card (MatrixTranslation.transverseIndices (fixedWeights d) H) ≤
        (⌊H⌋₊ + 1) ^ d.m ∧
      (∀ a ∈ MatrixTranslation.transverseIndices (fixedWeights d) H,
        ∀ i, a i < ⌊H⌋₊ + 1) ∧
      r.2.1 0 + 1 ≤ ⌊H / d.v0⌋₊ + 1 := by
  constructor
  · simpa using OAI.PiExponent.finiteFinset_box_card
      (MatrixTranslation.transverseIndices (fixedWeights d) H) (⌊H⌋₊ + 1)
      (fun a ha i => OAI.PiExponent.LiteralAnalytic.transverseIndices_coordinate_bound d H ⟨a, ha⟩ i)
  constructor
  · intro a ha i
    exact OAI.PiExponent.LiteralAnalytic.transverseIndices_coordinate_bound d H ⟨a, ha⟩ i
  · exact OAI.PiExponent.LiteralAnalytic.row_first_coordinate_bound d H r
