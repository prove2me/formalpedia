-- Prove2me | solution 1 for HedgeContract.OPE.eq_56
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:38:31.202319+00:00
-- url     : https://prove2.me/submissions/40faba09-3231-4deb-9351-fb54deefc40a

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

open HedgeContract.OPE

theorem solution (P : Params) (Z : ℝ) (hκ : 0 < P.κ) (hA : P.Alo ≤ P.Ahi) :
    Astar P Z ∈ Set.Icc P.Alo P.Ahi ∧
      ∀ A ∈ Set.Icc P.Alo P.Ahi,
        h P (Astar P Z) - Z * Astar P Z ≤ h P A - Z * A := by
  unfold Astar
  by_cases h1 : Z ≤ P.κ * P.Alo + P.b
  · rw [if_pos h1]
    refine ⟨⟨le_rfl, hA⟩, fun A hA' => ?_⟩
    obtain ⟨hl, hu⟩ := hA'
    unfold h
    nlinarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hl), hκ]
  · rw [if_neg h1]
    by_cases h2 : P.κ * P.Ahi + P.b ≤ Z
    · rw [if_pos h2]
      refine ⟨⟨hA, le_rfl⟩, fun A hA' => ?_⟩
      obtain ⟨hl, hu⟩ := hA'
      unfold h
      nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu), hκ]
    · rw [if_neg h2]
      push_neg at h1 h2
      have e : P.κ * ((Z - P.b) / P.κ) = Z - P.b := by field_simp
      refine ⟨⟨?_, ?_⟩, fun A hA' => ?_⟩
      · rw [le_div_iff₀ hκ]; linarith
      · rw [div_le_iff₀ hκ]; linarith
      · have key : h P A - Z * A - (h P ((Z - P.b) / P.κ) - Z * ((Z - P.b) / P.κ))
            = P.κ / 2 * (A - (Z - P.b) / P.κ) ^ 2 := by
          unfold h
          have : Z = P.κ * ((Z - P.b) / P.κ) + P.b := by linarith
          set s := (Z - P.b) / P.κ
          rw [this]; ring
        have : 0 ≤ P.κ / 2 * (A - (Z - P.b) / P.κ) ^ 2 := by positivity
        linarith
