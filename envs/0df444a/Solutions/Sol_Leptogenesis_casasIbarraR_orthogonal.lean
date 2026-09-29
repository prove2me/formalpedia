-- Prove2me | solution 1 for Leptogenesis.casasIbarraR_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T16:19:00.033424+00:00
-- url     : https://prove2.me/submissions/e8f9a405-7598-4325-bbcb-53540232fe40

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

set_option autoImplicit false

open Leptogenesis Matrix in
theorem solution (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses)
    (hpos : ∀ i, 0 < masses i) :
    (casasIbarraR v M lam U masses)ᵀ * casasIbarraR v M lam U masses = 1 ∧
      casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ = 1 := by
  obtain ⟨hU, _, hmU⟩ := hdiag
  set Ds : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => ((Real.sqrt (masses i) : ℂ))⁻¹) with hDs
  set Dt : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun k => ((Real.sqrt (M k) : ℂ))⁻¹) with hDt
  have hm : lightMassMatrix v M lam =
      ((v : ℂ) * (v : ℂ)) • (lam * (Dt * Dt) * lamᵀ) := by
    have hDD : Dt * Dt = diagonal (fun k => ((M k : ℂ))⁻¹) := by
      rw [hDt, diagonal_mul_diagonal]
      congr 1
      funext k
      have h1 : ((Real.sqrt (M k) : ℂ)) * (Real.sqrt (M k) : ℂ) = (M k : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM k).le]
      rw [← mul_inv, h1]
    rw [hDD]
    ext α β
    rw [Matrix.smul_apply, Matrix.mul_apply]
    simp only [lightMassMatrix, Matrix.mul_diagonal, transpose_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hU1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU2 : Uᵀ * U.map (starRingEnd ℂ) = 1 := by
    have h := congrArg Matrix.transpose hU1
    rw [transpose_mul, transpose_one] at h
    have hc : (Uᴴ)ᵀ = U.map (starRingEnd ℂ) := by
      ext i j
      simp
    rw [hc] at h
    exact h
  have hRRt : casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ =
      Ds * (Uᵀ * lightMassMatrix v M lam * U) * Ds := by
    rw [hm]
    simp only [casasIbarraR, transpose_smul, transpose_mul, hDs, hDt, diagonal_transpose,
      transpose_transpose, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hmid : Uᵀ * lightMassMatrix v M lam * U = diagonal (fun i => (masses i : ℂ)) := by
    rw [hmU]
    calc Uᵀ * (U.map (starRingEnd ℂ) * diagonal (fun i => (masses i : ℂ)) * Uᴴ) * U
        = (Uᵀ * U.map (starRingEnd ℂ)) * diagonal (fun i => (masses i : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (masses i : ℂ)) := by rw [hU1, hU2, Matrix.one_mul, Matrix.mul_one]
  have hfin : casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ = 1 := by
    rw [hRRt, hmid, hDs, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : (Real.sqrt (masses i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hpos i)).ne'
    have h1 : ((Real.sqrt (masses i) : ℂ)) * (Real.sqrt (masses i) : ℂ) = (masses i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
    rw [← h1]
    field_simp
  exact ⟨mul_eq_one_comm.mp hfin, hfin⟩
