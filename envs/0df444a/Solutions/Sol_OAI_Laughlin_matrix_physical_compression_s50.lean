-- Prove2me | solution 1 for OAI.Laughlin.matrix_physical_compression_s50
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:34:17.559893+00:00
-- url     : https://prove2.me/submissions/b0064841-7446-4f4d-b8a2-c58787d0799b

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix InnerProductSpace ComplexOrder
open Matrix

theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix J I ℂ) (C : Matrix I I ℂ)
    (hC : C.IsHermitian) (hG : ((Wᴴ*W)*C*(Wᴴ*W)).PosSemidef) :
    (W*C*Wᴴ).PosSemidef := by
  have hWCW : (W * C * Wᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hC.eq,
      Matrix.mul_assoc]
  refine PosSemidef.of_dotProduct_mulVec_nonneg hWCW fun x => ?_
  have hA : (Wᴴ * W).IsHermitian := isHermitian_conjTranspose_mul_self W
  obtain ⟨U, d, hspec, hUU, hUHU⟩ :
      ∃ (U : Matrix I I ℂ) (d : I → ℝ),
        Wᴴ * W = U * diagonal (Complex.ofReal ∘ d) * Uᴴ ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 := by
    refine ⟨(hA.eigenvectorUnitary : Matrix I I ℂ), hA.eigenvalues, ?_, ?_, ?_⟩
    · simpa [star_eq_conjTranspose, Matrix.mul_assoc] using hA.spectral_theorem
    · simpa [star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
    · simpa [star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let D : Matrix I I ℂ := diagonal (Complex.ofReal ∘ d)
  let Dinv : Matrix I I ℂ := diagonal (fun i => ((d i : ℂ))⁻¹)
  let y : I → ℂ := Uᴴ *ᵥ (Wᴴ *ᵥ x)
  have hy_zero : ∀ i : I, d i = 0 → y i = 0 := by
    intro i hdi
    let v : I → ℂ := U *ᵥ Pi.single i 1
    have hAv : (Wᴴ * W) *ᵥ v = 0 := by
      calc (Wᴴ * W) *ᵥ v
          = (U * D * Uᴴ) *ᵥ (U *ᵥ Pi.single i 1) := by rw [hspec]
        _ = U *ᵥ (D *ᵥ ((Uᴴ * U) *ᵥ Pi.single i 1)) := by
            simp only [mulVec_mulVec, Matrix.mul_assoc]
        _ = U *ᵥ (D *ᵥ Pi.single i 1) := by rw [hUHU, one_mulVec]
        _ = U *ᵥ 0 := by
            congr 1
            ext j
            by_cases hj : j = i <;> simp [D, mulVec_diagonal, Pi.single_apply, hj, hdi]
        _ = 0 := mulVec_zero U
    have hWv_norm : star (W *ᵥ v) ⬝ᵥ (W *ᵥ v) = 0 := by
      calc star (W *ᵥ v) ⬝ᵥ (W *ᵥ v)
          = (star (W *ᵥ v) ᵥ* W) ⬝ᵥ v := dotProduct_mulVec _ _ _
        _ = (star v ᵥ* (Wᴴ * W)) ⬝ᵥ v := by rw [star_mulVec, vecMul_vecMul]
        _ = star v ⬝ᵥ ((Wᴴ * W) *ᵥ v) := (dotProduct_mulVec _ _ _).symm
        _ = 0 := by rw [hAv, dotProduct_zero]
    have hWv : W *ᵥ v = 0 := dotProduct_star_self_eq_zero.mp hWv_norm
    calc y i
        = Pi.single i (1 : ℂ) ⬝ᵥ (Uᴴ *ᵥ (Wᴴ *ᵥ x)) := by simp [y]
      _ = star (Pi.single i (1 : ℂ)) ⬝ᵥ (Uᴴ *ᵥ (Wᴴ *ᵥ x)) := by
          congr 1; ext j; by_cases hj : j = i <;> simp [hj]
      _ = (star (Pi.single i (1 : ℂ)) ᵥ* Uᴴ) ⬝ᵥ (Wᴴ *ᵥ x) := dotProduct_mulVec _ _ _
      _ = star v ⬝ᵥ (Wᴴ *ᵥ x) := by rw [← star_mulVec]
      _ = (star v ᵥ* Wᴴ) ⬝ᵥ x := dotProduct_mulVec _ _ _
      _ = star (W *ᵥ v) ⬝ᵥ x := by rw [← star_mulVec]
      _ = 0 := by rw [hWv, star_zero, zero_dotProduct]
  have hDDinv : D *ᵥ (Dinv *ᵥ y) = y := by
    ext i
    simp only [D, Dinv, mulVec_diagonal, Function.comp_apply]
    by_cases hdi : d i = 0
    · simp [hdi, hy_zero i hdi]
    · have hdiC : (d i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdi
      rw [← mul_assoc, mul_inv_cancel₀ hdiC, one_mul]
  let u : I → ℂ := U *ᵥ (Dinv *ᵥ y)
  have hAu : (Wᴴ * W) *ᵥ u = Wᴴ *ᵥ x := by
    calc (Wᴴ * W) *ᵥ u
        = (U * D * Uᴴ) *ᵥ (U *ᵥ (Dinv *ᵥ y)) := by rw [hspec]
      _ = U *ᵥ (D *ᵥ ((Uᴴ * U) *ᵥ (Dinv *ᵥ y))) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = U *ᵥ (D *ᵥ (Dinv *ᵥ y)) := by rw [hUHU, one_mulVec]
      _ = U *ᵥ y := by rw [hDDinv]
      _ = (U * Uᴴ) *ᵥ (Wᴴ *ᵥ x) := by dsimp [y]; rw [mulVec_mulVec]
      _ = Wᴴ *ᵥ x := by rw [hUU, one_mulVec]
  have hquad : star x ⬝ᵥ ((W * C * Wᴴ) *ᵥ x) =
      star u ⬝ᵥ (((Wᴴ * W) * C * (Wᴴ * W)) *ᵥ u) := by
    calc star x ⬝ᵥ ((W * C * Wᴴ) *ᵥ x)
        = star x ⬝ᵥ (W *ᵥ (C *ᵥ (Wᴴ *ᵥ x))) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = (star x ᵥ* W) ⬝ᵥ (C *ᵥ (Wᴴ *ᵥ x)) := dotProduct_mulVec _ _ _
      _ = star (Wᴴ *ᵥ x) ⬝ᵥ (C *ᵥ (Wᴴ *ᵥ x)) := by
          rw [star_mulVec, conjTranspose_conjTranspose]
      _ = star ((Wᴴ * W) *ᵥ u) ⬝ᵥ (C *ᵥ ((Wᴴ * W) *ᵥ u)) := by rw [← hAu]
      _ = (star u ᵥ* (Wᴴ * W)ᴴ) ⬝ᵥ (C *ᵥ ((Wᴴ * W) *ᵥ u)) := by rw [star_mulVec]
      _ = (star u ᵥ* (Wᴴ * W)) ⬝ᵥ (C *ᵥ ((Wᴴ * W) *ᵥ u)) := by rw [hA.eq]
      _ = star u ⬝ᵥ ((Wᴴ * W) *ᵥ (C *ᵥ ((Wᴴ * W) *ᵥ u))) := (dotProduct_mulVec _ _ _).symm
      _ = star u ⬝ᵥ (((Wᴴ * W) * C * (Wᴴ * W)) *ᵥ u) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [hquad]
  exact hG.dotProduct_mulVec_nonneg u
