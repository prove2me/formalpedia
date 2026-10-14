-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.low_transverse_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T10:02:49.634957+00:00
-- url     : https://prove2.me/submissions/ff462e10-78d2-4dea-9d94-4a764a01b2d3

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
import Theorems.Thm_OAI_PiExponent_MatrixTranslation_transverse_cutoff_card_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_fixedWeights_pos

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  have h := OAI.PiExponent.MatrixTranslation.transverse_cutoff_card_le
    (fixedWeights d) H ((d.base.A : ℝ) * H)
    (OAI.PiExponent.LiteralAnalytic.fixedWeights_pos d)
  exact_mod_cast (show
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.base.A : ℝ) * H)).card) ≤
      (realWeightedSimplex (fixedWeights d) ((d.base.A : ℝ) * H)).card by
        simpa [indexWeight, MatrixTranslationBounds.weight, Transverse] using h)