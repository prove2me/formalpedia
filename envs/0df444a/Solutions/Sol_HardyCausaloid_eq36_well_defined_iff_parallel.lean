-- Prove2me | solution 1 for HardyCausaloid.eq36_well_defined_iff_parallel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T20:11:48.611052+00:00
-- url     : https://prove2.me/submissions/430e920e-875f-4fa9-b071-03609de7c008

import Theorems.Thm_HardyCausaloid_eq35_conditional_ratio
import Theorems.Thm_HardyCausaloid_eq37_value_ratio_of_lengths

open HardyCausaloid
theorem solution {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (C : Causaloid Setting Outcome) (hC : IsCausaloidOf C M)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) :
    CondWellDefined M α₁ F₂ Y₂ ↔ ∃ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂ := by
  have h35 := eq35_conditional_ratio M C hC hO α₁ F₂ Y₂
  have h37 := (eq37_value_ratio_of_lengths M C hC hO α₁ F₂ Y₂).1
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, h37 c h⟩
  · rintro ⟨c, h⟩
    refine ⟨c, fun s hz => (div_eq_iff hz).mpr ?_⟩
    rw [h35.2.2.1 s, h35.2.2.2 s, h, smul_dotProduct, smul_eq_mul]
