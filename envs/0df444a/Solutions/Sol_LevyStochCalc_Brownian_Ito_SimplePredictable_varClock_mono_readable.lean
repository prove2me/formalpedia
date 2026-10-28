-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:17.038996+00:00
-- url     : https://prove2.me/submissions/b3d5c039-6883-4cd2-bad1-1bfd2551eac0

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
theorem solution (c : Fin G.N → ℝ) {k l : ℕ} (h : k ≤ l) :
    G.varClock c k ≤ G.varClock c l := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.varClock
  have hsub : Finset.range k ⊆ Finset.range l := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
  by_cases hj : j < G.N
  · rw [dif_pos hj]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg hj]
