-- Prove2me | solution 1 for LevyStochCalc.exists_bound_fderiv_cutoffFun
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:53:14.030846+00:00
-- url     : https://prove2.me/submissions/754ddda1-d3bf-4bd1-b3bb-41e2b7edf47c

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}


theorem _root_.solution {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) : ∃ K₁ : ℝ, ∀ z, ‖fderiv ℝ (cutoffFun f k) z‖ ≤ K₁ := by
  have hc := (continuous_fderiv_cutoffFun hf k).norm
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : Fin n → ℝ) (2*k)).image hc).bddAbove
  refine ⟨max B 0, ?_⟩
  intro z
  by_cases hz : ‖z‖ ≤ 2*k
  · apply le_trans (hB (Set.mem_image_of_mem _ ?_)) (le_max_left _ _)
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  · rw [fderiv_cutoffFun_eq_zero hk (lt_of_not_ge hz), norm_zero]
    exact le_max_right _ _
