-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.centered_saving_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:32.96199+00:00
-- url     : https://prove2.me/submissions/e05b1db7-d8f2-4de4-92b3-c64ea205add9

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_norm_centered_le_of_approx
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_sum_scales_le

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by
  have h := norm_centered_le_of_approx A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ C E hmain hE hA₁ hA₂ hB₁ hB₂ hvA₂ hva₁ hvB₂ hvb₁
  have hs := sum_scales_le hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  calc
    _ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := h
    _ ≤ E * C * (4 * (T / L)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hE hC)
    _ = _ := by ring
end OAI.SevenEighths.CenteredMoment
