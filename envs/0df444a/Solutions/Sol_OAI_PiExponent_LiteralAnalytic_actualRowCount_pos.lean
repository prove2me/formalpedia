-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actualRowCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T09:37:35.742491+00:00
-- url     : https://prove2.me/submissions/baac2a21-a13d-4ed4-9d47-338fd83922f7

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
    0 < actualRowCount d H := by
  rw [actualRowCount]
  have hK : 0 < d.K := Nat.zero_lt_of_lt d.K_pos
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨0, ?_⟩⟩⟩
  simp [OAI.PiExponent.strictWeightedSimplex, OAI.PiExponent.realWeightedSimplex]
  exact ⟨le_of_lt hH, hH⟩
