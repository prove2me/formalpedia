-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.sum_scales_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:40.090992+00:00
-- url     : https://prove2.me/submissions/72004079-8a71-4b8f-b1c8-c9c2c74ddb2b

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_scale_le_product_div
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
theorem _root_.solution {X₁ X₂ Y₁ Y₂ T L : ℝ}
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    X₁ + X₂ + Y₁ + Y₂ ≤ 4 * (T / L) := by
  have a := scale_le_product_div (le_trans hL.le hX₁) hL hX₂ hprodX
  have b := scale_le_product_div (le_trans hL.le hX₂) hL hX₁
    (by simpa only [mul_comm] using hprodX)
  have c := scale_le_product_div (le_trans hL.le hY₁) hL hY₂ hprodY
  have d := scale_le_product_div (le_trans hL.le hY₂) hL hY₁
    (by simpa only [mul_comm] using hprodY)
  linarith
end OAI.SevenEighths.CenteredMoment
