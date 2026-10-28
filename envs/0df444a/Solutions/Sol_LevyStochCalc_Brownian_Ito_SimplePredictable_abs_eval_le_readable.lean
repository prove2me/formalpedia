-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.abs_eval_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:14.502014+00:00
-- url     : https://prove2.me/submissions/4b98715d-2eba-414f-9d81-726e540a13b0

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- At most one cell of a strictly monotone partition contains a given time. -/
theorem LevyStochCalc.Brownian.Ito.partition_cell_unique {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    {s : ℝ} {i j : Fin M} (hi : π i.castSucc < s ∧ s ≤ π i.succ)
    (hj : π j.castSucc < s ∧ s ≤ π j.succ) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (i.succ : Fin (M + 1)) ≤ j.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
    exact absurd (hi.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
  · have hle : (j.succ : Fin (M + 1)) ≤ i.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
    exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hi.1)
/-- A simple integrand evaluates to a tile's coefficient at every time in that tile. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.eval_of_mem_Ioc {T : ℝ} (H : SimplePredictable Ω T) (j : Fin H.N)
    {s : ℝ} (hs : H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) (ω : Ω) :
    H.eval s ω = H.ξ j ω := by
  classical
  unfold SimplePredictable.eval
  rw [Finset.sum_eq_single j
    (fun i _ hij => if_neg fun hc => hij (partition_cell_unique H.partition_strictMono hc hs))
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  exact if_pos hs
/-- A simple integrand with coefficients bounded by `C ≥ 0` has evaluations bounded by `C`. -/
theorem solution {T : ℝ} (H : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (i : Fin H.N) (ω : Ω), |H.ξ i ω| ≤ C) (s : ℝ) (ω : Ω) : |H.eval s ω| ≤ C := by
  classical
  by_cases h : ∃ j : Fin H.N, H.partition j.castSucc < s ∧ s ≤ H.partition j.succ
  · obtain ⟨j, hj⟩ := h
    rw [H.eval_of_mem_Ioc j hj ω]
    exact hC j ω
  · push Not at h
    have hz : H.eval s ω = 0 := by
      unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
      exact Finset.sum_eq_zero fun j _ =>
        if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz, abs_zero]
    exact hC0
