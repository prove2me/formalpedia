-- Prove2me | solution 1 for LevyStochCalc.Probability.measurableSet_predictableSigma_Ioc_prod
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:17:20.832947+00:00
-- url     : https://prove2.me/submissions/c33029b2-adc4-4958-b493-0be44fb7255e

import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

theorem _root_.solution {r q : ℝ} (hrq : r ≤ q) {A : Set Ω}
    (hA : MeasurableSet[ℱ r] A) :
    MeasurableSet[predictableSigma ℱ] (Set.Ioc r q ×ˢ A) := by
  have h : Set.Ioc r q ×ˢ A = (Set.Ioi r ×ˢ A) \ (Set.Ioi q ×ˢ A) := by
    ext ⟨s, ω⟩
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_Ioi, Set.mem_diff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, fun h => absurd h2 (not_le.2 h.1)⟩
    · rintro ⟨⟨h1, h3⟩, h4⟩
      exact ⟨⟨h1, le_of_not_gt fun h => h4 ⟨h, h3⟩⟩, h3⟩
  rw [h]
  exact (measurableSet_predictableSigma_Ioi_prod hA).diff
    (measurableSet_predictableSigma_Ioi_prod (ℱ.mono hrq _ hA))

end Cells

end LevyStochCalc.Probability
