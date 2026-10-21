-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_toReal_le_card_of_cube_cover
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T15:51:30.554759+00:00
-- url     : https://prove2.me/submissions/2e68f21f-ecf7-42f6-a5b8-1b758021d2ea

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hcover : weightedSimplexRegion w T ⊆ {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1})
    (hcubes : MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
      ((OAI.PiExponent.realWeightedSimplex w T).card : ENNReal)) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) ≤
      ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) := by
  have hvol : MeasureTheory.volume (weightedSimplexRegion w T) ≤ MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} := MeasureTheory.measure_mono hcover
  have hfinite :
      MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ OAI.PiExponent.realWeightedSimplex w T,
        ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} ≠ ⊤ := by
    rw [hcubes]
    simp
  have hreal := ENNReal.toReal_mono hfinite hvol
  simpa only [hcubes, ENNReal.toReal_natCast] using hreal
