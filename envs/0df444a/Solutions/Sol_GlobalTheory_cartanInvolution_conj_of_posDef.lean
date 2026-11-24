-- Prove2me | solution 1 for GlobalTheory.cartanInvolution_conj_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:25:58.828159+00:00
-- url     : https://prove2.me/submissions/42d915c2-70bc-40c1-8772-88c6013d05c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory
open scoped MatrixOrder
namespace GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]
end GlobalTheory
