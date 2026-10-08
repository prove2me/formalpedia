-- Prove2me | solution 1 for LocalRademacher.StarHull.tildeG_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:36:55.218988+00:00
-- url     : https://prove2.me/submissions/e1ecdc97-c6d3-45c3-8a57-2cad9dd93527

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

set_option autoImplicit false

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

open LocalRademacher.StarHull in
theorem solution {X : Type*} (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (r : ℝ) (hr : 0 < r)
    (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f) :
    tildeG F T r ⊆ localClass F T r := by
  rintro g ⟨f, hf, rfl⟩
  have hM : 0 < max (T f) r := lt_of_lt_of_le hr (le_max_right _ _)
  have hα0 : 0 ≤ r / max (T f) r := div_nonneg hr.le hM.le
  have hα1 : r / max (T f) r ≤ 1 := (div_le_one hM).2 (le_max_right _ _)
  refine ⟨⟨f, hf, r / max (T f) r, ⟨hα0, hα1⟩, ?_⟩, ?_⟩
  · funext x; simp
  · refine le_trans (hTsq f hf _ ⟨hα0, hα1⟩) ?_
    have h1 : T f ≤ max (T f) r := le_max_left _ _
    have h2 : r ≤ max (T f) r := le_max_right _ _
    have hTf := hT0 f hf
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : r ^ 2 * T f ≤ r ^ 2 * max (T f) r := mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ r * max (T f) r)]
