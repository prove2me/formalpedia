-- Prove2me | solution 1 for LinearOptimization.ellipsoid_update_matrix_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-09T17:07:37.971842+00:00
-- url     : https://prove2.me/submissions/b6ed70a4-3a83-4de8-91d2-ed1c23442d94

import Definitions.Def_LinearOptimization_EllipsoidMethod
import Mathlib.Tactic

open Matrix

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (LinearOptimization.ellipsoidUpdateMatrix D a).PosDef := by
  classical
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hDt : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · unfold LinearOptimization.ellipsoidUpdateMatrix
    apply Matrix.IsHermitian.smul
    · apply Matrix.IsHermitian.sub hD.isHermitian
      apply Matrix.IsHermitian.smul
      apply Matrix.IsHermitian.smul
      have haHerm : (vecMulVec a a : Matrix (Fin n) (Fin n) ℝ).IsHermitian := by
        ext i j
        simp [vecMulVec, mul_comm]
      simpa [hDt] using Matrix.isHermitian_mul_mul_conjTranspose D haHerm
      exact isSelfAdjoint_iff.mpr (by simp)
      exact isSelfAdjoint_iff.mpr (by simp)
    · exact isSelfAdjoint_iff.mpr (by simp)
  · intro x hx
    have hs : 0 < x ⬝ᵥ D.mulVec x := hD.dotProduct_mulVec_pos hx
    let q : ℝ := a ⬝ᵥ D.mulVec a
    let p : ℝ := a ⬝ᵥ D.mulVec x
    let s : ℝ := x ⬝ᵥ D.mulVec x
    have hq' : 0 < q := by simpa [q] using hq
    have hs' : 0 < s := by simpa [s] using hs
    have hnonneg := hD.posSemidef.dotProduct_mulVec_nonneg
      (x - (p / q) • a)
    have hsymm : x ⬝ᵥ D.mulVec a = p := by
      dsimp [p]
      have hv : x ᵥ* D = Dᵀ.mulVec x := by
        simpa using Matrix.vecMul_transpose Dᵀ x
      calc
        x ⬝ᵥ D.mulVec a = x ᵥ* D ⬝ᵥ a := Matrix.dotProduct_mulVec _ _ _
        _ = Dᵀ.mulVec x ⬝ᵥ a := by rw [hv]
        _ = D.mulVec x ⬝ᵥ a := by rw [hDt]
        _ = a ⬝ᵥ D.mulVec x := dotProduct_comm _ _
    have hcs : p ^ 2 ≤ q * s := by
      simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
        smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
      rw [hsymm] at hnonneg
      change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
      have hmul := mul_nonneg hq'.le hnonneg
      field_simp [ne_of_gt hq'] at hmul
      nlinarith
    have hquad :
        x ⬝ᵥ (D * vecMulVec a a * D).mulVec x = p ^ 2 := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.vecMulVec_mulVec]
      simp [Matrix.mulVec_smul, dotProduct_smul, hsymm, p, pow_two]
    unfold LinearOptimization.ellipsoidUpdateMatrix
    simp only [star_trivial, Matrix.smul_mulVec, Matrix.sub_mulVec,
      dotProduct_smul, dotProduct_sub, smul_eq_mul]
    rw [hquad]
    change 0 < ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
      (s - (2 / ((n : ℝ) + 1)) * (q⁻¹ * p ^ 2))
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
    have hden : 0 < (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hα : 0 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) :=
      div_pos (sq_pos_of_pos hnpos) hden
    have hγ0 : 0 ≤ (2 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hγ1 : (2 : ℝ) / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hpq : q⁻¹ * p ^ 2 ≤ s := by
      rw [inv_mul_eq_div, div_le_iff₀ hq']
      simpa [mul_comm] using hcs
    have hpq0 : 0 ≤ q⁻¹ * p ^ 2 := by positivity
    apply mul_pos hα
    nlinarith [mul_le_mul_of_nonneg_left hpq hγ0]
