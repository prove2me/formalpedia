-- Prove2me | solution 1 for IsotropicSpin.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:55:50.610043+00:00
-- url     : https://prove2.me/submissions/fe4eb0ab-3eb1-4300-9fa4-0c698e0e3f84

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_omega
import Definitions.Def_IsotropicSpin_yMat

open scoped Matrix Matrix.Norms.L2Operator

namespace Aux_Iso_17
open IsotropicSpin Matrix
open scoped Matrix Matrix.Norms.L2Operator

theorem herm (k : Fin 3) : (spinOne k)ᴴ = spinOne k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [spinOne, Matrix.conjTranspose_apply, Complex.conj_ofReal]

theorem hY (ξ : Fin 3 → ℂ) : (yMat ξ)ᴴ = ∑ k, star (ξ k) • spinOne k := by
  unfold yMat
  rw [conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [conjTranspose_smul, herm]

theorem lin (φ : Fin 3 → ℂ) (c : Fin 3 → Fin 3 → ℂ) (M : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) :
    star φ ⬝ᵥ ((∑ l, ∑ k, c l k • M l k) *ᵥ φ) = ∑ l, ∑ k, c l k * (star φ ⬝ᵥ (M l k *ᵥ φ)) := by
  simp only [sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem form (φ ξ : Fin 3 → ℂ) :
    star ξ ⬝ᵥ (omega φ *ᵥ ξ) =
      (1 / 2 : ℂ) * (star ((yMat ξ)ᴴ *ᵥ φ) ⬝ᵥ ((yMat ξ)ᴴ *ᵥ φ)) := by
  obtain ⟨G, hG⟩ : ∃ G : Fin 3 → Fin 3 → ℂ,
      G = fun k l => star φ ⬝ᵥ ((spinOne l * spinOne k) *ᵥ φ) := ⟨_, rfl⟩
  have hom : omega φ = Matrix.of fun k l => (1 / 2 : ℂ) * G k l := by rw [hG]; rfl
  have h2 : star ((yMat ξ)ᴴ *ᵥ φ) ⬝ᵥ ((yMat ξ)ᴴ *ᵥ φ) =
      ∑ l, ∑ k, (ξ l * star (ξ k)) * G k l := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec, hY]
    unfold yMat
    rw [Finset.sum_mul_sum]
    simp_rw [smul_mul_smul_comm]
    rw [lin, hG]
  rw [h2, hom]
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Aux_Iso_17

open IsotropicSpin Matrix Aux_Iso_17 in
open scoped Matrix Matrix.Norms.L2Operator in
theorem solution (φ ξ : Fin 3 → ℂ) (hφ : WHAdditivity.Renyi.IsUnitVector φ)
    (hξ : WHAdditivity.Renyi.IsUnitVector ξ) :
    (star ξ ⬝ᵥ (omega φ *ᵥ ξ)).im = 0 ∧
      (star ξ ⬝ᵥ (omega φ *ᵥ ξ)).re ≤ 1 / 2 * ‖(yMat ξ)ᴴ * yMat ξ‖ := by
  rw [form]
  set w := (yMat ξ)ᴴ *ᵥ φ with hw
  have hww : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hww]
  constructor
  · simp
  · have hre : ((1 / 2 : ℂ) * ((∑ i, Complex.normSq (w i) : ℝ) : ℂ)).re =
        1 / 2 * ∑ i, Complex.normSq (w i) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [hre]
    have hbound := l2_opNorm_mulVec (yMat ξ)ᴴ ((EuclideanSpace.equiv (Fin 3) ℂ).symm φ)
    have hnφ : ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm φ‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      have : ∑ i, ‖((EuclideanSpace.equiv (Fin 3) ℂ).symm φ) i‖ ^ 2 = 1 := by
        unfold WHAdditivity.Renyi.IsUnitVector at hφ
        rw [← hφ]
        apply Finset.sum_congr rfl
        intro i _
        rw [Complex.sq_norm]
        rfl
      rw [this, Real.sqrt_one]
    rw [hnφ, mul_one] at hbound
    have hnw : ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm ((yMat ξ)ᴴ *ᵥ ((EuclideanSpace.equiv (Fin 3) ℂ).symm φ))‖ ^ 2
        = ∑ i, Complex.normSq (w i) := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      rw [Complex.sq_norm]
      rfl
    have hsq : ‖(yMat ξ)ᴴ‖ ^ 2 = ‖(yMat ξ)ᴴ * yMat ξ‖ := by
      rw [l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose]; ring
    have hn0 : 0 ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm ((yMat ξ)ᴴ *ᵥ ((EuclideanSpace.equiv (Fin 3) ℂ).symm φ))‖ :=
      norm_nonneg _
    have := pow_le_pow_left₀ hn0 hbound 2
    rw [hnw, hsq] at this
    linarith
