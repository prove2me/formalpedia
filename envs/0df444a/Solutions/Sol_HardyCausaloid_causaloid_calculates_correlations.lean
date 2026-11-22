-- Prove2me | solution 1 for HardyCausaloid.causaloid_calculates_correlations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:39:11.327876+00:00
-- url     : https://prove2.me/submissions/2be8515d-9c34-4331-b23e-379e67076879

import Theorems.Thm_HardyCausaloid_causaloid_exists
import Theorems.Thm_HardyCausaloid_eq35_conditional_ratio
import Theorems.Thm_HardyCausaloid_eq36_well_defined_iff_parallel
import Theorems.Thm_HardyCausaloid_eq37_value_ratio_of_lengths

open HardyCausaloid

theorem solution {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (Ω₁ : ∀ x, Finset (Label Setting Outcome x))
    (hΩ₁ : ∀ x, Fiducial (elemTable M x) (Ω₁ x)) :
    (∃ C : Causaloid Setting Outcome, C.Ω₁ = Ω₁ ∧ IsCausaloidOf C M) ∧
    ∀ C : Causaloid Setting Outcome, IsCausaloidOf C M →
    ∀ (O₁ O₂ : Finset X), Disjoint O₁ O₂ → ∀ (α₁ : Lab Setting Outcome O₁)
      (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)),
      (Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
          C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))) ∧
        ∀ s, Summable (fun β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)) =>
          regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s)) ∧
      (∀ s, condNum M α₁ F₂ Y₂ s = condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s ∧
        condDen M α₁ F₂ s = condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) ∧
      (CondWellDefined M α₁ F₂ Y₂ ↔ ∃ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
      (∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c → condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
      (condB C α₁ F₂ ≠ 0 → ∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c →
        c = euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)) ∧
      (condB C α₁ F₂ = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0) := by
  refine ⟨causaloid_exists M Ω₁ hΩ₁, ?_⟩
  intro C hC O₁ O₂ hO α F Y
  obtain ⟨vsum, psum, num, den⟩ := eq35_conditional_ratio M C hC hO α F Y
  exact ⟨⟨vsum, psum⟩, fun s => ⟨num s, den s⟩,
    eq36_well_defined_iff_parallel M C hC hO α F Y, eq37_value_ratio_of_lengths M C hC hO α F Y⟩
