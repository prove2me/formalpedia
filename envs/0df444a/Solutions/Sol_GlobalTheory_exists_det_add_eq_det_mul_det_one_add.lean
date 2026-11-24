-- Prove2me | solution 1 for GlobalTheory.exists_det_add_eq_det_mul_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:08.833259+00:00
-- url     : https://prove2.me/submissions/ab2bdb87-803b-48e7-a294-5504f93fcb92

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open scoped MatrixOrder
namespace GlobalTheory
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hd : P.det ≠ 0) :
    ∃ R : Matrix n n ℂ, R.PosSemidef ∧ (R = 0 → Q = 0) ∧ (P + Q).det = P.det * (1 + R).det := by
  have hP0 : (0 : Matrix n n ℂ) ≤ P := nonneg_iff_posSemidef.mpr hP
  set S := CFC.sqrt P with hSdef
  have hS0 : (0 : Matrix n n ℂ) ≤ S := CFC.sqrt_nonneg P
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP0
  have hSh : Sᴴ = S := (nonneg_iff_posSemidef.mp hS0).1
  have hdS : S.det ≠ 0 := by
    intro h
    apply hd
    rw [← hSS, det_mul, h, zero_mul]
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hdS
  have hl : S * S⁻¹ = 1 := mul_nonsing_inv S hSu
  have hr : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
  have hback : S * (S⁻¹ * Q * S⁻¹) * S = Q := by
    calc S * (S⁻¹ * Q * S⁻¹) * S = (S * S⁻¹) * Q * (S⁻¹ * S) := by
          simp only [Matrix.mul_assoc]
      _ = Q := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]
  refine ⟨S⁻¹ * Q * S⁻¹, ?_, ?_, ?_⟩
  · have h := hQ.conjTranspose_mul_mul_same S⁻¹
    rwa [conjTranspose_nonsing_inv, hSh] at h
  · intro h
    rw [← hback, h, Matrix.mul_zero, Matrix.zero_mul]
  · have hPQ : P + Q = S * (1 + S⁻¹ * Q * S⁻¹) * S := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, hback]
    rw [hPQ, det_mul, det_mul, ← hSS, det_mul]
    ring
end GlobalTheory
