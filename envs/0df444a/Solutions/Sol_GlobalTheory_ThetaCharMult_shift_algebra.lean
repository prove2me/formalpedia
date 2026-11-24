-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.shift_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:11.604183+00:00
-- url     : https://prove2.me/submissions/dd3201f8-10e0-4dd0-b1c4-cbd48d540e69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaCharMult
variable {g : ℕ}
namespace GlobalTheory.ThetaCharMult
theorem _root_.solution (A B C D τ σ J : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm) (hσ : σ.IsSymm)
    (h1 : J * (C * τ + D) = 1) (h2 : (C * τ + D) * J = 1) (hs : σ = (A * τ + B) * J)
    (hA : A - σ * C = Jᵀ) (hCD : D * Cᵀ - C * Dᵀ = 0) (a b z a' b' : Fin g → ℂ)
    (ha' : a' = Aᵀ *ᵥ a + Cᵀ *ᵥ b) (hb' : b' = Bᵀ *ᵥ a + Dᵀ *ᵥ b) :
    Jᵀ *ᵥ (z + τ *ᵥ a' + b') = Jᵀ *ᵥ z + σ *ᵥ a + b ∧
    (z + τ *ᵥ a' + b') ⬝ᵥ ((J * C) *ᵥ (z + τ *ᵥ a' + b')) +
        2 * (-(a' ⬝ᵥ (τ *ᵥ a')) / 2 - a' ⬝ᵥ (z + b')) =
      z ⬝ᵥ ((J * C) *ᵥ z) + (a ⬝ᵥ b - a' ⬝ᵥ b') +
        2 * (-(a ⬝ᵥ (σ *ᵥ a)) / 2 - a ⬝ᵥ (Jᵀ *ᵥ z + b)) := by
  set j := C * τ + D with hj
  have hjT : jᵀ = τ * Cᵀ + Dᵀ := by rw [hj, transpose_add, transpose_mul, hτ.eq]
  have hjσ : jᵀ * σ = τ * Aᵀ + Bᵀ := by
    conv_lhs => rw [← hσ.eq]
    rw [← transpose_mul, hs, Matrix.mul_assoc, h1, Matrix.mul_one, transpose_add, transpose_mul,
      hτ.eq]
  set p := σ *ᵥ a + b with hp
  set q := τ *ᵥ a' + b' with hq
  have hqp : jᵀ *ᵥ p = q := by
    rw [hp, hq, ha', hb', mulVec_add, mulVec_mulVec, hjσ, hjT]
    simp only [add_mulVec, mulVec_add, mulVec_mulVec]
    abel
  have hpq : Jᵀ *ᵥ q = p := by
    rw [← hqp, mulVec_mulVec, ← transpose_mul, h2, transpose_one, one_mulVec]
  have hM : (J * C).IsSymm := by
    have e : C * jᵀ = j * Cᵀ := by
      rw [hjT, hj, Matrix.mul_add, Matrix.add_mul, sub_eq_zero.mp hCD, Matrix.mul_assoc]
    show (J * C)ᵀ = J * C
    calc (J * C)ᵀ = (J * j) * Cᵀ * Jᵀ := by rw [h1, Matrix.one_mul, transpose_mul]
      _ = J * (C * jᵀ) * Jᵀ := by rw [e]; simp only [Matrix.mul_assoc]
      _ = J * C * (J * j)ᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [h1, transpose_one, Matrix.mul_one]
  have hq1 : ∀ x, q ⬝ᵥ ((J * C) *ᵥ x) = a' ⬝ᵥ x - a ⬝ᵥ (Jᵀ *ᵥ x) := by
    intro x
    have e1 : q ⬝ᵥ ((J * C) *ᵥ x) = p ⬝ᵥ (C *ᵥ x) := by
      rw [← hpq, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    have e2 : a' ⬝ᵥ x = a ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ (C *ᵥ x) := by
      rw [ha', add_dotProduct, mulVec_transpose, mulVec_transpose, dotProduct_mulVec,
        dotProduct_mulVec]
    have e3 : (σ *ᵥ a) ⬝ᵥ (C *ᵥ x) = a ⬝ᵥ (σ *ᵥ (C *ᵥ x)) := by
      rw [dot_mulVec_symm hσ, dotProduct_comm]
    rw [e1, e2, ← hA, sub_mulVec, dotProduct_sub, hp, add_dotProduct, e3, mulVec_mulVec]
    ring
  have hz : z + τ *ᵥ a' + b' = z + q := by rw [hq, add_assoc]
  rw [hz]
  refine ⟨by rw [mulVec_add, hpq, hp, add_assoc], ?_⟩
  have e4 := dot_mulVec_symm hM q z
  have e5 := hq1 z
  have e6 := hq1 q
  rw [hpq] at e6
  have e7 : a' ⬝ᵥ q = a' ⬝ᵥ (τ *ᵥ a') + a' ⬝ᵥ b' := by rw [hq, dotProduct_add]
  have e8 : a ⬝ᵥ p = a ⬝ᵥ (σ *ᵥ a) + a ⬝ᵥ b := by rw [hp, dotProduct_add]
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [e4, e5, e6, e7, e8]
  ring
end GlobalTheory.ThetaCharMult
