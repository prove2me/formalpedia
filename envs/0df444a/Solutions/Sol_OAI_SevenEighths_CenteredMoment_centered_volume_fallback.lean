-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.centered_volume_fallback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:35.247463+00:00
-- url     : https://prove2.me/submissions/44fcf42a-1c9c-4e58-a9ec-4fdaa01a9d54

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

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution (A₁ A₂ B₁ B₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T C : ℝ)
    (hA₁ : ‖A₁‖ ≤ C * X₁) (hA₂ : ‖A₂‖ ≤ C * X₂)
    (hB₁ : ‖B₁‖ ≤ C * Y₁) (hB₂ : ‖B₂‖ ≤ C * Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 2 * C ^ 2 * T := by
  have hA := mul_le_mul hA₁ hA₂ (norm_nonneg A₂) ((norm_nonneg A₁).trans hA₁)
  have hB := mul_le_mul hB₁ hB₂ (norm_nonneg B₂) ((norm_nonneg B₁).trans hB₁)
  have h := norm_sub_le (A₁ * A₂) (B₁ * B₂)
  rw [norm_mul, norm_mul] at h
  have heX : C * X₁ * (C * X₂) = C ^ 2 * T := by rw [← hprodX]; ring
  have heY : C * Y₁ * (C * Y₂) = C ^ 2 * T := by rw [← hprodY]; ring
  rw [heX] at hA
  rw [heY] at hB
  linarith
end OAI.SevenEighths.CenteredMoment
