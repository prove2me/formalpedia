-- Prove2me | solution 1 for HasBoundedCoveringNumber.subset
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:40:44.748601+00:00
-- url     : https://prove2.me/submissions/1afde418-95bb-4f55-b33a-18152b1a9b49

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

theorem _root_.solution {B : Set T}
    (h : HasBoundedCoveringNumber A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasBoundedCoveringNumber B (2 ^ d * c) d := by
  refine ⟨lt_of_le_of_lt (Metric.ediam_mono hBA) h.ediam_lt_top, fun ε hε => ?_⟩
  have h2 : ((ε / 2 : ℝ≥0) : ℝ≥0∞) ≤ Metric.ediam A := by
    refine le_trans ?_ (hε.trans (Metric.ediam_mono hBA))
    exact_mod_cast (NNReal.half_le_self ε)
  have h1 := h.coveringNumber_le (ε / 2) h2
  have h3 : (coveringNumber ε B : ℝ≥0∞) ≤ (coveringNumber (ε / 2) A : ℝ≥0∞) := by
    exact_mod_cast coveringNumber_subset_le hBA
  refine h3.trans (h1.trans (le_of_eq ?_))
  have e : ((ε / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ = 2 * (ε : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.coe_div two_ne_zero, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp),
      inv_inv]
    simp
  rw [e, ENNReal.mul_rpow_of_nonneg _ _ hd]
  ring
