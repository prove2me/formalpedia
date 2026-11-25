-- Prove2me | solution 1 for Newton.trace_conjTranspose_mul_self_re_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:17.056109+00:00
-- url     : https://prove2.me/submissions/5925da4a-cd72-4a36-89fa-5dd088d30559

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_Newton_Gauge_LieAlgebra
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
import Theorems.Thm_Newton_star_mul_self_re_nonneg
import Theorems.Thm_Newton_Complex_re_finset_sum
attribute [local simp] Newton.SuNAlgebra.lie_matrix

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M ≠ 0) : (trace (conjTranspose M * M)).re > 0 := by
  have h_exists : ∃ i j, M i j ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    apply hM
    ext i j
    exact h_all_zero i j
  obtain ⟨i₀, j₀, h_ne⟩ := h_exists
  unfold trace diag
  simp only [conjTranspose_apply, mul_apply]
  rw [Complex.re_finset_sum]
  apply Finset.sum_pos'
  · intro i _
    rw [Complex.re_finset_sum]
    apply Finset.sum_nonneg
    intro j _
    exact star_mul_self_re_nonneg (M j i)
  · use j₀, Finset.mem_univ j₀
    rw [Complex.re_finset_sum]
    apply Finset.sum_pos'
    · intro j _
      exact star_mul_self_re_nonneg (M j j₀)
    · use i₀, Finset.mem_univ i₀
      have h_pos : Complex.normSq (M i₀ j₀) > 0 := Complex.normSq_pos.mpr h_ne
      have h_eq : (star (M i₀ j₀) * M i₀ j₀).re = Complex.normSq (M i₀ j₀) := by
        set z := M i₀ j₀
        simp only [Complex.star_def]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
                   Complex.normSq_apply]
      rw [h_eq]
      exact h_pos
end Newton
