-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.comp_sum_ite_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:21.775341+00:00
-- url     : https://prove2.me/submissions/4fc4c8fe-2ec5-44cd-bd43-7ed5ddedfce0

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A function fixing `0` commutes with a step sum over a strictly monotone partition. -/
theorem solution {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f : Fin M → ℝ) (s : ℝ) (g : ℝ → ℝ) (hg0 : g 0 = 0) :
    g (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g (f j) else 0 := by
  classical
  by_cases h : ∃ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ → j = j₀ := by
      intro j hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (j.succ : Fin (M + 1)) ≤ j₀.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
        exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hj₀.1)
      · have hle : (j₀.succ : Fin (M + 1)) ≤ j.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
        exact absurd (hj₀.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
    have hsum : ∀ h : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h j else 0) = h j₀ := by
      intro h
      rw [Finset.sum_eq_single j₀ (fun j _ hjne => if_neg fun hc => hjne (huniq j hc))
        (fun hnm => absurd (Finset.mem_univ _) hnm)]
      exact if_pos hj₀
    rw [hsum f, hsum fun j => g (f j)]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz f, hz fun j => g (f j), hg0]
