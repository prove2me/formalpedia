-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.norm_centered_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:39.469205+00:00
-- url     : https://prove2.me/submissions/ba30bb4d-70e2-48b5-be3f-9130d8487086

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_ofResidueMask_keep_one
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_MaskedCharacter_value_mul
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_normTwist_mul
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_coefficient_mul
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_centered_error_identity
attribute [local simp] OAI.SevenEighths.CenteredMoment.ofResidueMask_keep_one
attribute [local simp] OAI.SevenEighths.CenteredMoment.MaskedCharacter.value_mul
attribute [local simp] OAI.SevenEighths.CenteredMoment.normTwist_mul
attribute [local simp] OAI.SevenEighths.CenteredMoment.coefficient_mul

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤
      ‖A₁ - a₁‖ * ‖A₂‖ + ‖a₁‖ * ‖A₂ - a₂‖ +
        ‖B₁ - b₁‖ * ‖B₂‖ + ‖b₁‖ * ‖B₂ - b₂‖ := by
  rw [centered_error_identity A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain]
  calc
    _ ≤ ‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) - (B₁ - b₁) * B₂‖ +
        ‖b₁ * (B₂ - b₂)‖ := norm_sub_le _ _
    _ ≤ (‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂)‖ +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(A₁ - a₁) * A₂‖ + ‖a₁ * (A₂ - a₂)‖) +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp only [norm_mul]
end OAI.SevenEighths.CenteredMoment
