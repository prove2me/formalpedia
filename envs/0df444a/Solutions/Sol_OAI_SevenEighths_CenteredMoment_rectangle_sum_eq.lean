-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.rectangle_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:52.860594+00:00
-- url     : https://prove2.me/submissions/d3183e79-210d-45ec-9e4e-0b3b3ffd83bb

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
theorem _root_.solution (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (a * b) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
        plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂ := by
  simp only [plainSum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [coefficient_mul, rectangle]
  ring
end OAI.SevenEighths.CenteredMoment
