-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.slot_rectangle_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:28.806399+00:00
-- url     : https://prove2.me/submissions/c5ad13d9-2734-4352-8976-2f8d03b67628

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_rectangle_sum_eq
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
    (p : M) (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (p * (a * b)) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      coefficient d N t p *
        (plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
          plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂) := by
  rw [← rectangle_sum_eq]
  simp only [coefficient_mul, Finset.mul_sum, mul_assoc]
end OAI.SevenEighths.CenteredMoment
