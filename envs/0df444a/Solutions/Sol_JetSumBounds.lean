-- Prove2me | solution 1 for JetSumBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:13:34.727576+00:00
-- url     : https://prove2.me/submissions/310d8a89-b65e-456e-a671-ce71959246e7

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetSumBounds

set_option autoImplicit false

theorem _root_.solution :
    (∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (U : Set Plane),
        IsOpen U → ∀ (i : ℕ) (E₁ E₂ : Plane → Z),
        ContDiffOn ℝ (⊤ : ℕ∞) E₁ U → ContDiffOn ℝ (⊤ : ℕ∞) E₂ U →
        ∀ x ∈ U, iteratedFDeriv ℝ i (fun z => E₁ z + E₂ z) x
          = iteratedFDeriv ℝ i E₁ x + iteratedFDeriv ℝ i E₂ x)
      ∧ (∀ (W : Type) [NormedAddCommGroup W] (a₁ a₂ : W) (q Q : ℝ),
          ‖a₁‖ ≤ q → ‖a₂‖ ≤ q → 2 * q ≤ Q → ‖a₁ + a₂‖ ≤ Q)
      ∧ (∀ (W : Type) [NormedAddCommGroup W] (a₁ a₂ b₁ b₂ : W) (q Q t : ℝ),
          ‖a₁ - b₁‖ ≤ q * t → ‖a₂ - b₂‖ ≤ q * t → 2 * q ≤ Q → 0 ≤ t →
          ‖(a₁ + a₂) - (b₁ + b₂)‖ ≤ Q * t) := by
  refine ⟨?_, ?_, ?_⟩
  -- (1) Additivity of the order-`i` jet on an open set.
  · intro Z _ _ U hUo i E₁ E₂ h1 h2 x hx
    have hu : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
    have e0 : iteratedFDeriv ℝ i (fun z => E₁ z + E₂ z) x
        = iteratedFDerivWithin ℝ i (fun z => E₁ z + E₂ z) U x :=
      (iteratedFDerivWithin_of_isOpen i hUo hx).symm
    have e1 : iteratedFDeriv ℝ i E₁ x = iteratedFDerivWithin ℝ i E₁ U x :=
      (iteratedFDerivWithin_of_isOpen i hUo hx).symm
    have e2 : iteratedFDeriv ℝ i E₂ x = iteratedFDerivWithin ℝ i E₂ U x :=
      (iteratedFDerivWithin_of_isOpen i hUo hx).symm
    rw [e0, e1, e2]
    exact iteratedFDerivWithin_add_apply
      ((h1.contDiffWithinAt hx).of_le (by exact_mod_cast le_top))
      ((h2.contDiffWithinAt hx).of_le (by exact_mod_cast le_top)) hu hx
  -- (2) Sup bounds add, at the cost of the factor two.
  · intro W _ a₁ a₂ q Q h1 h2 hQ
    calc ‖a₁ + a₂‖ ≤ ‖a₁‖ + ‖a₂‖ := norm_add_le _ _
      _ ≤ Q := by linarith
  -- (3) Two-point bounds add.  The rearrangement first, then the triangle inequality.
  · intro W _ a₁ a₂ b₁ b₂ q Q t h1 h2 hQ ht
    have hrw : (a₁ + a₂) - (b₁ + b₂) = (a₁ - b₁) + (a₂ - b₂) :=
      (sub_add_sub_comm _ _ _ _).symm
    rw [hrw]
    calc ‖(a₁ - b₁) + (a₂ - b₂)‖ ≤ ‖a₁ - b₁‖ + ‖a₂ - b₂‖ := norm_add_le _ _
      _ ≤ q * t + q * t := by linarith
      _ = (2 * q) * t := by ring
      _ ≤ Q * t := mul_le_mul_of_nonneg_right hQ ht
