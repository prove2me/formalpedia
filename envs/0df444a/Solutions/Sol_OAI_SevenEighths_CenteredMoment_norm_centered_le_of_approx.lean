-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.norm_centered_le_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:19.904961+00:00
-- url     : https://prove2.me/submissions/2d312f74-7c7d-498e-89b2-f5d6c660c09d

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Basic
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_norm_centered_le

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := by
  have h₁ := mul_le_mul hA₁ hvA₂ (norm_nonneg A₂) hE
  have h₂ := mul_le_mul hA₂ hva₁ (norm_nonneg a₁) hE
  have h₃ := mul_le_mul hB₁ hvB₂ (norm_nonneg B₂) hE
  have h₄ := mul_le_mul hB₂ hvb₁ (norm_nonneg b₁) hE
  have h := norm_centered_le A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain
  nlinarith
end OAI.SevenEighths.CenteredMoment
