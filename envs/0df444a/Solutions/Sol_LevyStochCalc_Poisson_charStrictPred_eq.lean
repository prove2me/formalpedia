-- Prove2me | solution 1 for LevyStochCalc.Poisson.charStrictPred_eq
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T07:09:51.956143+00:00
-- url     : https://prove2.me/submissions/7447a8e9-72a5-4a6b-92b2-dd2d866bfaf5

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}



theorem _root_.solution (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} {A : Set E} {b T : ℝ} (hT : 0 < T) (hbT : b < T)
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A) (s : ℝ) (ω : Ω) :
    charStrictPred N w Bfam A T e₀ s ω = charStrict N w Bfam s ω := by
  unfold charStrictPred
  by_cases hs : 0 < s
  · have hp : 0 < min s T := lt_min hs hT
    rw [predStrict_eq N w Bfam hp (min_le_right _ _) he₀ ω]
    have hsets (j : ι) :
        Bfam j ∩ Set.Ioo (0 : ℝ) (min s T) ×ˢ (Set.univ : Set E) =
        Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ (Set.univ : Set E) := by
      ext q
      constructor
      · intro hq
        exact ⟨hq.1, ⟨⟨hq.2.1.1, lt_of_lt_of_le hq.2.1.2 (min_le_left _ _)⟩, hq.2.2⟩⟩
      · intro hq
        exact ⟨hq.1, ⟨⟨hq.2.1.1, lt_min hq.2.1.2 ((hBsub j hq.1).1.2.trans_lt hbT)⟩, trivial⟩⟩
    simp only [charStrict, hsets]
  · have hs' : s ≤ 0 := le_of_not_gt hs
    rw [predStrict_of_nonpos N w Bfam A T ((min_le_left s T).trans hs') e₀ ω]
    have hzero : Set.Ioo (0 : ℝ) s = ∅ := Set.Ioo_eq_empty_of_le hs'
    simp [charStrict, hzero]
