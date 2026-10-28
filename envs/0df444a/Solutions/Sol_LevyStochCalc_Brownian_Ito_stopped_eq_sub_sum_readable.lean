-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:32.55261+00:00
-- url     : https://prove2.me/submissions/72050280-75ca-4698-90e4-1322435e4ed4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoOptionalStopping.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section Stopped
variable (τ : Ω → WithTop ℝ)
omit [IsProbabilityMeasure P] in
/-- **The pathwise decomposition of the cut integrand.** On the window `(0, t]` the integrand cut
off at `τ` is the integrand minus, for each value `c` the stopping time can take below `t`, the
piece it carries on `(c, t]`. -/
theorem solution (H : Ω → ℝ → ℝ) {t : ℝ} (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    LevyStochCalc.Brownian.Ito.indTerm (LevyStochCalc.Probability.stopped τ H) 0 t
      = fun ω s => LevyStochCalc.Brownian.Ito.indTerm H 0 t ω s - ∑ c ∈ J, LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω s := by
  classical
  funext ω s
  simp only [LevyStochCalc.Brownian.Ito.indTerm]
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
  · have hind0 : LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s = 1 := by simp [LevyStochCalc.Brownian.Ito.indIoc, hs]
    have hzero : ∀ c ∈ J, τ ω ≠ ((c : ℝ) : WithTop ℝ) → LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω s = 0 := by
      intro c _ hne
      simp [LevyStochCalc.Brownian.Ito.cutTerm, LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_notMem (show ω ∉ {ω | τ ω = ((c : ℝ) :
        WithTop ℝ)} from hne)]
    rcases hτJ ω with ⟨c₀, hc₀J, hc₀⟩ | hge
    · have hsum : ∑ c ∈ J, LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω s = LevyStochCalc.Brownian.Ito.cutTerm τ H c₀ t ω s := by
        refine Finset.sum_eq_single_of_mem c₀ hc₀J fun c hc hne => ?_
        refine hzero c hc ?_
        rw [hc₀]
        exact fun hcc => hne (by exact_mod_cast hcc.symm)
      have hhit : LevyStochCalc.Brownian.Ito.hitInd τ c₀ ω = 1 := by
        simp [LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_mem (show ω ∈ {ω | τ ω = ((c₀ : ℝ) : WithTop ℝ)} from hc₀)]
      rw [hsum, hind0, LevyStochCalc.Brownian.Ito.cutTerm, hhit]
      by_cases hsc : s ≤ c₀
      · have h1 : LevyStochCalc.Probability.stopped τ H ω s = H ω s := by
          rw [LevyStochCalc.Probability.stopped, if_pos]
          rw [hc₀]
          exact_mod_cast hsc
        have h2 : LevyStochCalc.Brownian.Ito.indIoc Ω c₀ t ω s = 0 := by
          simp only [LevyStochCalc.Brownian.Ito.indIoc]
          rw [Set.indicator_of_notMem]
          exact fun hmem => absurd hmem.1 (not_lt.mpr hsc)
        rw [h1, h2]
        ring
      · push Not at hsc
        have h1 : LevyStochCalc.Probability.stopped τ H ω s = 0 := by
          rw [LevyStochCalc.Probability.stopped, if_neg]
          rw [hc₀]
          exact fun hcon => absurd (by exact_mod_cast hcon : s ≤ c₀) (not_le.mpr hsc)
        have h2 : LevyStochCalc.Brownian.Ito.indIoc Ω c₀ t ω s = 1 := by
          simp [LevyStochCalc.Brownian.Ito.indIoc, Set.indicator_of_mem (show s ∈ Set.Ioc c₀ t from ⟨hsc, hs.2⟩)]
        rw [h1, h2]
        ring
    · have hsum : ∑ c ∈ J, LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω s = 0 := by
        refine Finset.sum_eq_zero fun c hc => hzero c hc ?_
        intro hcon
        rw [hcon] at hge
        exact absurd (by exact_mod_cast hge : t ≤ c) (not_le.mpr (hJt c hc))
      have h1 : LevyStochCalc.Probability.stopped τ H ω s = H ω s := by
        rw [LevyStochCalc.Probability.stopped, if_pos]
        exact le_trans (by exact_mod_cast hs.2) hge
      rw [hsum, hind0, h1]
      ring
  · have hind0 : LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s = 0 := by
      simp only [LevyStochCalc.Brownian.Ito.indIoc]
      exact Set.indicator_of_notMem hs _
    have hsum : ∑ c ∈ J, LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω s = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hnot : s ∉ Set.Ioc c t := by
        intro hmem
        exact hs ⟨lt_of_le_of_lt (hJ0 c hc) hmem.1, hmem.2⟩
      have hz : LevyStochCalc.Brownian.Ito.indIoc Ω c t ω s = 0 := by
        simp only [LevyStochCalc.Brownian.Ito.indIoc]
        exact Set.indicator_of_notMem hnot _
      simp [LevyStochCalc.Brownian.Ito.cutTerm, hz]
    rw [hsum, hind0]
    ring
