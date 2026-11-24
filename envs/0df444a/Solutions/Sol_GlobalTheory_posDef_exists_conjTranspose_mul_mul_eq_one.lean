-- Prove2me | solution 1 for GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:08.514878+00:00
-- url     : https://prove2.me/submissions/8e0adadc-3f38-4a10-ab65-c425447402c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]
end GlobalTheory
