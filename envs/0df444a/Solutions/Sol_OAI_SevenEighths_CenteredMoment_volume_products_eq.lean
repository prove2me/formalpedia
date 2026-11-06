-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.volume_products_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:29.42819+00:00
-- url     : https://prove2.me/submissions/bdc7e065-ca0d-4b00-8d0e-9f52c5970ffa

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
theorem _root_.solution (c I₁ I₂ : ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hscale : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm c I₁ t X₁ * volumeTerm c I₂ t X₂ =
      volumeTerm c I₁ t Y₁ * volumeTerm c I₂ t Y₂ := by
  have hpow : (X₁ : ℂ) ^ (1 + Complex.I * t) *
      (X₂ : ℂ) ^ (1 + Complex.I * t) =
      (Y₁ : ℂ) ^ (1 + Complex.I * t) * (Y₂ : ℂ) ^ (1 + Complex.I * t) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hX₁ hX₂,
      ← Complex.mul_cpow_ofReal_nonneg hY₁ hY₂, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hscale]
  unfold volumeTerm
  calc
    _ = c ^ 2 * I₁ * I₂ *
      ((X₁ : ℂ) ^ (1 + Complex.I * t) * (X₂ : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [hpow]; ring
end OAI.SevenEighths.CenteredMoment
