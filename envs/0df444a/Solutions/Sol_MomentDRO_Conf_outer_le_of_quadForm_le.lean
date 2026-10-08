-- Prove2me | solution 1 for MomentDRO.Conf.outer_le_of_quadForm_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:14:19.794249+00:00
-- url     : https://prove2.me/submissions/5f765f4c-c8c8-417c-8b99-5e46aae055ba

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

set_option autoImplicit false

namespace P324c4c9e

open Matrix

lemma dot_mulVec_symm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.transpose = A)
    (x y : Fin m → ℝ) : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

lemma cs {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.transpose = A)
    (hpos : ∀ u : Fin m → ℝ, 0 ≤ u ⬝ᵥ (A *ᵥ u)) (x y : Fin m → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have key : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (A *ᵥ y)) * (t * t) + (2 * (x ⬝ᵥ (A *ᵥ y))) * t
      + (x ⬝ᵥ (A *ᵥ x)) := by
    intro t
    have h := hpos (x + t • y)
    have hs := dot_mulVec_symm A hA x y
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
    rw [hs] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

end P324c4c9e

open MomentDRO.Conf Matrix in
theorem solution {m : ℕ}
    (cov : Matrix (Fin m) (Fin m) ℝ) (hcov : cov.PosDef)
    (d : Fin m → ℝ) (b : ℝ)
    (hd : quadForm cov⁻¹ d ≤ b) :
    LoewnerLE (Matrix.vecMulVec d d) (b • cov) := by
  have hT : cov.transpose = cov := by
    have h1 := hcov.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    exact h1
  have hpos : ∀ u : Fin m → ℝ, 0 ≤ u ⬝ᵥ (cov *ᵥ u) := by
    intro u
    have := hcov.posSemidef.dotProduct_mulVec_nonneg u
    simpa using this
  set y := cov⁻¹ *ᵥ d with hy
  have hcy : cov *ᵥ y = d := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hcov.isUnit),
      Matrix.one_mulVec]
  have hqy : y ⬝ᵥ (cov *ᵥ y) = quadForm cov⁻¹ d := by
    rw [hcy, quadForm, dotProduct_comm]
  show (b • cov - Matrix.vecMulVec d d).PosSemidef
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_smul, hT, Matrix.transpose_vecMulVec]
  · intro x
    have hcs := P324c4c9e.cs cov hT hpos x y
    rw [hqy, hcy] at hcs
    have hx := hpos x
    have hv : Matrix.vecMulVec d d *ᵥ x = (d ⬝ᵥ x) • d := by
      ext i
      simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e : star x ⬝ᵥ ((b • cov - Matrix.vecMulVec d d) *ᵥ x)
        = b * (x ⬝ᵥ (cov *ᵥ x)) - (x ⬝ᵥ d) ^ 2 := by
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm d x]
      ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hd hx]
