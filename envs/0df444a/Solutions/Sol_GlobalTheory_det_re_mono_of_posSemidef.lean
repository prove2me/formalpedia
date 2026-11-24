-- Prove2me | solution 1 for GlobalTheory.det_re_mono_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:03.943812+00:00
-- url     : https://prove2.me/submissions/4af73feb-9fa9-4648-acd8-e37e5d7fa842

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd
import Theorems.Thm_GlobalTheory_exists_det_add_eq_det_mul_det_one_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
private lemma det_one_add_eq_prod_eigenvalues {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℂ}
    (hR : R.PosSemidef) :
    (1 + R).det = ((∏ i, (1 + hR.1.eigenvalues i) : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hR.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hspec : R = U * diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) * star U := by
    conv_lhs => rw [hR.1.spectral_theorem]
    rfl
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hR.1.eigenvectorUnitary.2
  have hdU : U.det * (star U).det = 1 := by rw [← det_mul, hUU, det_one]
  have h1 : 1 + R = U * diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) * star U := by
    have hd1 : diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) =
        1 + diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) := by
      rw [← diagonal_one, diagonal_add]
      rfl
    rw [hd1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hspec]
  rw [h1, det_mul, det_mul, det_diagonal, mul_right_comm, hdU, one_mul]
  push_cast
  rfl
private lemma exists_one_le_det_one_add_of_posSemidef {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℂ}
    (hR : R.PosSemidef) :
    ∃ c : ℝ, (1 + R).det = c ∧ 1 ≤ c ∧ (c ≤ 1 → R = 0) := by
  refine ⟨∏ i, (1 + hR.1.eigenvalues i), det_one_add_eq_prod_eigenvalues hR, ?_, ?_⟩
  · exact Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i)
  · intro hc
    apply hR.1.eigenvalues_eq_zero_iff.mp
    funext j
    have hj : 1 + hR.1.eigenvalues j ≤ ∏ i, (1 + hR.1.eigenvalues i) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      exact le_mul_of_one_le_right (by linarith [hR.eigenvalues_nonneg j])
        (Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i))
    have := hR.eigenvalues_nonneg j
    simp only [Pi.zero_apply]
    linarith
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef →
      0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧
        (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0) := by
  intro n _ _ P Q hP hQ
  obtain ⟨hPre, hPim⟩ := Complex.nonneg_iff.mp hP.det_nonneg
  obtain ⟨hSre, -⟩ := Complex.nonneg_iff.mp (hP.add hQ).det_nonneg
  by_cases hd : P.det = 0
  · refine ⟨hPre, ?_, fun h => absurd hd h⟩
    rw [hd, Complex.zero_re]
    exact hSre
  · obtain ⟨R, hR, hR0, hdet⟩ := exists_det_add_eq_det_mul_det_one_add hP hQ hd
    obtain ⟨c, hc, hc1, hcR⟩ := exists_one_le_det_one_add_of_posSemidef hR
    have hre : (P + Q).det.re = P.det.re * c := by
      rw [hdet, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hpos : 0 < P.det.re := by
      rcases hPre.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by rw [← h, Complex.zero_re]) (by rw [← hPim, Complex.zero_im])) hd
    refine ⟨hPre, ?_, fun _ hle => hR0 (hcR ?_)⟩
    · rw [hre]
      exact le_mul_of_one_le_right hPre hc1
    · rw [hre] at hle
      by_contra hlt
      have : P.det.re * 1 < P.det.re * c := mul_lt_mul_of_pos_left (not_le.mp hlt) hpos
      linarith
end GlobalTheory
