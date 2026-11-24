-- Prove2me | solution 1 for GlobalTheory.BigCell.skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:32.509279+00:00
-- url     : https://prove2.me/submissions/1bd32722-2ee4-4278-85eb-2db23ca04804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
open GlobalTheory GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)
namespace GlobalTheory.BigCell
theorem _root_.solution (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔtf : Δt.map f = Δt) (hNf : N.map f = N)
    (hNtf : Nt.map f = Nt) (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0)
    (hD : (Nt * G * N) * D' = 1) :
    (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f = 0 := by
  have hΔtT : Δtᵀ = Δ := by rw [← hΔT, transpose_transpose]
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hDf : Nt * (G.map f * (N * D'.map f)) = 1 := by
    have := congrArg (Matrix.map · f) hD
    simp only [Matrix.map_mul, hNtf, hNf, Matrix.map_one f (map_zero f) (map_one f)] at this
    simpa only [Matrix.mul_assoc] using this
  have hDt : ∀ {γ : Type} (X : Matrix β γ R), D'ᵀ * (Nt * (Gᵀ * (N * X))) = X := by
    intro γ X
    have := congrArg transpose hD
    rw [transpose_mul, transpose_mul, transpose_mul, hNT, hNtT, transpose_one] at this
    calc D'ᵀ * (Nt * (Gᵀ * (N * X))) = (D'ᵀ * (Nt * (Gᵀ * N))) * X := by simp only [Matrix.mul_assoc]
      _ = X := by rw [this, Matrix.one_mul]
  have hxT : (Δt * G * N * D')ᵀ = D'ᵀ * (Nt * (Gᵀ * Δ)) := by
    simp only [transpose_mul, hNT, hΔtT, Matrix.mul_assoc]
  have hxf : (Δt * G * N * D').map f = Δt * (G.map f * (N * D'.map f)) := by
    simp only [Matrix.map_mul, hΔtf, hNf, Matrix.mul_assoc]
  have hY : Nt * (Gᵀ * ((Δ * J * Nt + N * J * Δt) * (G.map f * (N * D'.map f)))) = 0 := by
    rw [e6, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      show Gᵀ * (K * (G.map f * (N * D'.map f))) = K * N * D'.map f by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG, Matrix.mul_assoc],
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, e7, Matrix.zero_mul, smul_zero]
  calc (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f
      = D'ᵀ * (Nt * (Gᵀ * ((Δ * J * Nt + N * J * Δt) * (G.map f * (N * D'.map f))))) := by
        rw [hxT, hxf]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hDf, hDt, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.mul_zero]
end GlobalTheory.BigCell
