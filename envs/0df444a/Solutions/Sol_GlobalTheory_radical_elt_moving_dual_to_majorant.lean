-- Prove2me | solution 1 for GlobalTheory.radical_elt_moving_dual_to_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:27.384866+00:00
-- url     : https://prove2.me/submissions/2e4d3503-1952-4adf-8aa1-065cf4adbd99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.conjTranspose = J) (hθ : θ * θ = 1) (hQ : (J * θ).PosDef)
    (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ) (hXX : X₂.conjTranspose * J * X₂ = 0)
    (hYY : Y₂.conjTranspose * J * Y₂ = 0) (hXY : X₂.conjTranspose * J * Y₂ = 1) :
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  have hθJ : θᴴ * J = J * θ := by
    have := hQ.isHermitian.eq
    rwa [conjTranspose_mul, hJ] at this
  have hYX : Y₂ᴴ * J * X₂ = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hinj : Function.Injective X₂.mulVec := by
    intro a b hab
    have := congrArg (fun v => (Y₂ᴴ * J).mulVec v) hab
    simpa [Matrix.mulVec_mulVec, hYX] using this
  have hP : (X₂ᴴ * (J * θ) * X₂).PosDef := hQ.conjTranspose_mul_mul_same hinj
  obtain ⟨P, hPdef⟩ : ∃ P, P = X₂ᴴ * (J * θ) * X₂ := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPiH : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.isHermitian.eq]
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = θ * X₂ * P⁻¹ := ⟨_, rfl⟩
  have hXY' : X₂ᴴ * J * Y' = 1 := by
    rw [← hPPi, hY', hPdef]; simp only [Matrix.mul_assoc]
  have hY'Y' : Y'ᴴ * J * Y' = 0 := by
    have h1 : ∀ B : Matrix (Fin n) (Fin p) ℂ, θᴴ * (J * (θ * B)) = J * B := by
      intro B
      rw [← Matrix.mul_assoc, hθJ, Matrix.mul_assoc, ← Matrix.mul_assoc θ, hθ, Matrix.one_mul]
    have h2 : X₂ᴴ * (J * (X₂ * P⁻¹)) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
    rw [hY']
    simp only [conjTranspose_mul, hPiH, Matrix.mul_assoc, h1, h2, Matrix.mul_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Y' - Y₂ := ⟨_, rfl⟩
  have hXD : X₂ᴴ * J * D = 0 := by rw [hD, Matrix.mul_sub, hXY', hXY, sub_self]
  have hDX : Dᴴ * J * X₂ = 0 := by
    have := congrArg conjTranspose hXD
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hkey : Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D = 0 := by
    rw [hD]
    simp only [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] at hY'Y' hYY ⊢
    rw [hY'Y', hYY]
    abel

  have tXX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have tXD : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (D * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXD, Matrix.zero_mul]
  have tDX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), Dᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have tXY : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (Y₂ * B)) = B := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have hXX' : X₂ᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hXX]
  have hXD' : X₂ᴴ * (J * D) = 0 := by rw [← Matrix.mul_assoc, hXD]
  have hDX' : Dᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hDX]
  have hXY'' : X₂ᴴ * (J * Y₂) = 1 := by rw [← Matrix.mul_assoc, hXY]
  obtain ⟨E, hE⟩ : ∃ E, E = Dᴴ * J * Y₂ := ⟨_, rfl⟩
  have hE' : Dᴴ * (J * Y₂) = E := by rw [hE, Matrix.mul_assoc]
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ,
      u = 1 + (D * X₂ᴴ * J - X₂ * Dᴴ * J + X₂ * E * X₂ᴴ * J) := ⟨_, rfl⟩
  have huJ : uᴴ * J * u = J := by
    have hexp : uᴴ * J * u = J + J * X₂ * (Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D) * X₂ᴴ * J := by
      rw [hu, hE]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_one,
        conjTranspose_conjTranspose, hJ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, tXX, tXD, tDX,
        hXX', hXD', hDX', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]
      abel
    rw [hexp, hkey]; simp
  have huX : u * X₂ = X₂ := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXX', hDX',
      Matrix.mul_zero, add_zero, sub_zero]
  have huY : u * Y₂ = Y' := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXY'',
      Matrix.mul_one, hE']
    rw [hD]; abel
  have hdetJ : J.det ≠ 0 := by
    intro h0
    have := hQ.det_pos
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact lt_irrefl _ this
  have hudet : IsUnit u.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetJ ?_
    have := congrArg Matrix.det huJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have huU : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).mpr hudet
  refine ⟨huU.unit, ?_, ?_, ?_, ?_⟩
  · simpa using huJ
  · simpa using huX
  · intro v hv
    have hv' : X₂ᴴ *ᵥ (J *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec]; exact hv
    refine ⟨-(Dᴴ *ᵥ (J *ᵥ v)), ?_⟩
    simp only [IsUnit.unit_spec, hu, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero, Matrix.mulVec_neg]
    abel
  · simp only [IsUnit.unit_spec, huY, hY', Matrix.mul_assoc, hPiP, Matrix.mul_one]
end GlobalTheory
