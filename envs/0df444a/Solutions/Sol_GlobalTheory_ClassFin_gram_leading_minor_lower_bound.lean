-- Prove2me | solution 1 for GlobalTheory.ClassFin.gram_leading_minor_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:37.875481+00:00
-- url     : https://prove2.me/submissions/d494bc69-76ad-4a10-8046-a3ecaa2e13ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_exists_shift
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_det_mono
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_posDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution :
    ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  intro N g hg
  obtain ⟨k, hk0, hk1, hkQ⟩ := gramLB_exists_shift (gramLB_posDef hg)
  refine ⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩
  set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ
  set E : Fin j → Fin N := Fin.castLE hj with hE
  let C : Matrix (Fin N) (Fin j) ℝ := Γ.submatrix id E
  let Cz : Matrix (Fin N) (Fin j) ℤ := γ.submatrix id E
  have hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C := by
    have e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id,
      Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]
  have hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hΓdet : Γ.det ≠ 0 := by
    have e := (Int.castRingHom ℝ).map_det γ
    rw [show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]
    simpa using hγ
  have hCinj : Function.Injective C.mulVec := by
    have hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E := by
      rw [← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id,
        Matrix.mul_one]
    have hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec := by
      intro x y hxy
      funext a
      have hEinj : Function.Injective E := Fin.castLE_injective hj
      have e := congrFun hxy (E a)
      simpa [mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff] using e
    rw [hC]
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)
  have hCC : (Cᵀ * C).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact PosDef.conjTranspose_mul_self C hCinj
  have hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hkQ.conjTranspose_mul_mul_same C
  have hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hdet1 : 1 ≤ (Cᵀ * C).det := by
    have hpos := hCC.det_pos
    rw [hCz, ← RingHom.map_det, eq_intCast] at hpos
    rw [hCz, ← RingHom.map_det, eq_intCast]
    have hz : 0 < (Czᵀ * Cz).det := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det := hz
    exact_mod_cast hz1
  calc k ^ N ≤ k ^ j := pow_le_pow_of_le_one hk0.le hk1 hj
    _ ≤ k ^ j * (Cᵀ * C).det := le_mul_of_one_le_right (pow_nonneg hk0.le _) hdet1
    _ = (k • (Cᵀ * C)).det := by rw [det_smul, Fintype.card_fin]
    _ ≤ (k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C).det := gramLB_det_mono (hCC.smul hk0) hQ'
    _ = _ := by rw [← hsplit, ← hGram]
end GlobalTheory.ClassFin
