-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:41.315992+00:00
-- url     : https://prove2.me/submissions/023168ee-2699-414b-b69c-fb09cdff200e

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- Two right-continuous processes that agree a.s. at each time of `[0, T]` agree, almost surely,
at every time of `[0, T]` simultaneously. -/
theorem solution {A B : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, A t ω = B t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T → A (q : ℝ) ω = B (q : ℝ) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [h (q : ℝ) hq] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ hq' => absurd hq' hq
  have hend : ∀ᵐ ω ∂P, (0 : ℝ) ≤ T → A T ω = B T ω := by
    by_cases hT : (0 : ℝ) ≤ T
    · filter_upwards [h T ⟨hT, le_rfl⟩] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ hT' => absurd hT' hT
  filter_upwards [hA, hB, hrat, hend] with ω hAω hBω hqω hTω
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq]
    exact hTω (ht.1.trans ht.2)
  · have hex : ∀ k : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (t + 1 / ((k : ℝ) + 1)) T := by
      intro k
      refine exists_rat_btwn (lt_min ?_ hlt)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    choose q hq1 hq2 using hex
    have hqIcc : ∀ k, ((q k : ℝ)) ∈ Set.Icc (0 : ℝ) T := fun k =>
      ⟨(ht.1.trans_lt (hq1 k)).le, ((hq2 k).trans_le (min_le_right _ _)).le⟩
    have htend : Filter.Tendsto (fun k : ℕ => (q k : ℝ)) Filter.atTop
        (nhdsWithin t (Set.Ioi t)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.Eventually.of_forall fun k => hq1 k⟩
      have hub : ∀ k : ℕ, (q k : ℝ) ≤ t + 1 / ((k : ℝ) + 1) := fun k =>
        ((hq2 k).trans_le (min_le_left _ _)).le
      have hlb : ∀ k : ℕ, t ≤ (q k : ℝ) := fun k => (hq1 k).le
      have hupper : Filter.Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) Filter.atTop (nhds t) := by
        have := tendsto_const_nhds (x := t) (f := Filter.atTop (α := ℕ)) |>.add
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hlb hub
    have h1 := (hAω t).comp htend
    have h2 := (hBω t).comp htend
    have heqq : ((fun s => A s ω) ∘ fun k : ℕ => (q k : ℝ))
        = ((fun s => B s ω) ∘ fun k : ℕ => (q k : ℝ)) :=
      funext fun k => hqω (q k) (hqIcc k)
    rw [heqq] at h1
    exact tendsto_nhds_unique h1 h2
