-- Prove2me | solution 1 for Leptogenesis.lightMassMatrix_mulVec_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T16:18:59.415381+00:00
-- url     : https://prove2.me/submissions/690a84bb-0da3-4186-bef0-f3515d7f9a85

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

set_option autoImplicit false

open Leptogenesis Matrix in
theorem solution (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ)
    (hM : ∀ k, 0 < M k) (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses)
    (x : Fin 3 → ℂ) :
    ∑ α, ‖(lightMassMatrix v M lam *ᵥ star x) α‖ ^ 2 ≤
      (⨆ i, masses i) ^ 2 * ∑ α, ‖x α‖ ^ 2 := by
  obtain ⟨hU, h0, hmU⟩ := hdiag
  have hnsq : ∀ w : Fin 3 → ℂ, ((∑ α, ‖w α‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Complex.star_def, Complex.conj_mul']
  have hiso : ∀ (A : Matrix (Fin 3) (Fin 3) ℂ), Aᴴ * A = 1 → ∀ w : Fin 3 → ℂ,
      ∑ α, ‖(A *ᵥ w) α‖ ^ 2 = ∑ α, ‖w α‖ ^ 2 := by
    intro A hA w
    apply Complex.ofReal_injective
    rw [hnsq, hnsq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]
  have hU1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU3 : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU2 : Uᵀ * U.map (starRingEnd ℂ) = 1 := by
    have h := congrArg Matrix.transpose hU1
    rw [transpose_mul, transpose_one] at h
    have hc : (Uᴴ)ᵀ = U.map (starRingEnd ℂ) := by
      ext i j
      simp
    rw [hc] at h
    exact h
  have hcU : (U.map (starRingEnd ℂ))ᴴ * U.map (starRingEnd ℂ) = 1 := by
    have hc : (U.map (starRingEnd ℂ))ᴴ = Uᵀ := by
      ext i j
      simp
    rw [hc, hU2]
  have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [conjTranspose_conjTranspose, hU3]
  set S : ℝ := ⨆ i, masses i with hS
  have hle : ∀ i, masses i ^ 2 ≤ S ^ 2 := by
    intro i
    exact pow_le_pow_left₀ (h0 i) (le_ciSup (Set.finite_range masses).bddAbove i) 2
  rw [hmU, ← mulVec_mulVec, ← mulVec_mulVec, hiso _ hcU]
  set z : Fin 3 → ℂ := Uᴴ *ᵥ star x with hz
  have hzx : ∑ α, ‖z α‖ ^ 2 = ∑ α, ‖x α‖ ^ 2 := by
    rw [hz, hiso _ hUH]
    simp [Pi.star_apply]
  rw [← hzx, Finset.mul_sum]
  refine Finset.sum_le_sum (fun α _ => ?_)
  rw [mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 α),
    mul_pow]
  exact mul_le_mul_of_nonneg_right (hle α) (by positivity)
