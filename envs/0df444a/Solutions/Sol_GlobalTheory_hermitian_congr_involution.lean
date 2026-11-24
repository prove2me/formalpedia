-- Prove2me | solution 1 for GlobalTheory.hermitian_congr_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:19.581522+00:00
-- url     : https://prove2.me/submissions/c3cd89e0-d199-4fa2-8a49-248f898bb8a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution

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
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0) :
    ∃ R s : Matrix ι ι ℂ, R.det ≠ 0 ∧ sᴴ = s ∧ s * s = 1 ∧ Rᴴ * s * R = H := by
  have hA : H.IsHermitian := hH
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set d := hA.eigenvalues with hdd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hdd, hi]; simp)
  set s : Matrix ι ι ℂ := diagonal fun i => if 0 < d i then 1 else -1 with hs
  set D : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt |d i| : ℝ) : ℂ) with hD
  have key : D * s * D = diagonal (RCLike.ofReal ∘ d) := by
    rw [hD, hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : ((Real.sqrt |d i| : ℝ) : ℂ) * ((Real.sqrt |d i| : ℝ) : ℂ) = ((|d i| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Function.comp_apply]
    split_ifs with h
    · rw [mul_one, hsq, abs_of_pos h]; rfl
    · rw [mul_neg_one, neg_mul, hsq, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hd0 i))]
      push_cast; ring_nf; rfl
  have hDH : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]; congr 1; funext i; simp
  have hsH : sᴴ = s := by
    rw [hs, diagonal_conjTranspose]; congr 1; funext i; by_cases h : 0 < d i <;> simp [h]
  have hss : s * s = 1 := by
    rw [hs, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hR : (D * star U)ᴴ * s * (D * star U) = H := by
    rw [conjTranspose_mul, hDH, star_eq_conjTranspose, conjTranspose_conjTranspose]
    conv_rhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← key]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose]
    rfl
  refine ⟨D * star U, s, ?_, hsH, hss, hR⟩
  intro h0
  apply hd
  rw [← hR, det_mul, det_mul, h0, mul_zero]
end _root_.GlobalTheory
end GlobalTheory
