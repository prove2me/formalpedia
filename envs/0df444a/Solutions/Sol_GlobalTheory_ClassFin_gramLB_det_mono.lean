-- Prove2me | solution 1 for GlobalTheory.ClassFin.gramLB_det_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:40.972182+00:00
-- url     : https://prove2.me/submissions/c89b5acc-a117-4eaa-8ba9-25297a8fc175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_shift
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_one_le_det

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
open scoped MatrixOrder
namespace GlobalTheory.ClassFin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hP.1 0
  simp only [zero_smul, add_zero] at hEq
  have hd : ∀ i, 0 < hP.1.eigenvalues i := hP.eigenvalues_pos
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  let s : n → ℝ := fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹
  let B : Matrix n n ℝ := U * diagonal s
  have hBt : Bᴴ = diagonal s * Uᴴ := by
    simp [B]
  have hBPB : Bᴴ * P * B = 1 := by
    rw [hBt, hEq]
    simp only [B, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
      diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s]
    field_simp
    try nlinarith [hs, Real.sq_sqrt (hd i).le]
  have hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B := by
    rw [Matrix.mul_add, Matrix.add_mul, hBPB]
  have h1 : Bᴴ.det * B.det * P.det = 1 := by
    have e := congrArg det hBPB
    rw [det_mul, det_mul, det_one] at e
    linear_combination e
  have h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det := by
    rw [← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]
    ring
  have h3 : 1 ≤ (1 + Bᴴ * Q * B).det := by
    rw [add_comm]
    exact gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)
  have hc : 0 < Bᴴ.det * B.det := by
    have := hP.det_pos
    by_contra hneg
    nlinarith [not_lt.mp hneg]
  exact le_of_mul_le_mul_left (by linarith) hc
end GlobalTheory.ClassFin
