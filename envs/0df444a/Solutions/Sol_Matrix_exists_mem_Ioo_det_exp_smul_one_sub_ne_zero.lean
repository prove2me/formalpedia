-- Prove2me | solution 1 for Matrix.exists_mem_Ioo_det_exp_smul_one_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:37:54.824864+00:00
-- url     : https://prove2.me/submissions/d296c6a1-313d-4595-9569-f9a4b9125871

import Mathlib

open Matrix Complex Filter Topology Set

namespace RH10

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma abs_re_quad_le (D : Matrix n n ℂ) (x : n → ℂ) :
    |(star x ⬝ᵥ (D *ᵥ x)).re| ≤ (∑ i, ∑ j, ‖D i j‖) * (star x ⬝ᵥ x).re := by
  have hS : (star x ⬝ᵥ x).re = ∑ k, ‖x k‖ ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have hpair : ∀ i j, ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖ ^ 2 := by
    intro i j
    have hi : ‖x i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have hj : ‖x j‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
  rw [hS]
  calc |(star x ⬝ᵥ (D *ᵥ x)).re| ≤ ‖star x ⬝ᵥ (D *ᵥ x)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖D i j‖ * (‖x i‖ * ‖x j‖) := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
        rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
        ring
    _ ≤ ∑ i, ∑ j, ‖D i j‖ * ∑ k, ‖x k‖ ^ 2 := by
        gcongr with i _ j _
        exact hpair i j
    _ = (∑ i, ∑ j, ‖D i j‖) * ∑ k, ‖x k‖ ^ 2 := by
        rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]


lemma exists_angle_det_ne_zero (W : Matrix n n ℂ) :
    ∃ α ∈ Ioo 0 (2 * Real.pi), (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - W).det ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set f : ℝ → ℂ := fun α => exp ((α : ℂ) * I)
  have hinj : InjOn f (Ioo 0 (2 * Real.pi)) := by
    intro α hα β hβ h
    obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp h
    have him := congr_arg Complex.im hk
    simp at him
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) < 1 := by
        by_contra h'; push_neg at h'
        nlinarith [hα.1, hα.2, hβ.1, hβ.2, Real.pi_pos]
      have h2 : (-1 : ℝ) < k := by
        by_contra h'; push_neg at h'
        nlinarith [hα.1, hα.2, hβ.1, hβ.2, Real.pi_pos]
      have : k < 1 := by exact_mod_cast h1
      have : -1 < k := by exact_mod_cast h2
      omega
    rw [hk0] at him; simp at him; linarith
  have hsub : f '' Ioo 0 (2 * Real.pi) ⊆ (W.charpoly.roots.toFinset : Set ℂ) := by
    rintro _ ⟨α, hα, rfl⟩
    have hz := hcon α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (Matrix.charpoly_monic W).ne_zero, Polynomial.IsRoot,
      eval_charpoly, scalar_apply, ← smul_one_eq_diagonal]
    exact hz
  exact Set.Ioo_infinite (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi)
    (Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hinj)

end RH10

open Matrix

open Complex Set

theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) :
    ∃ α ∈ Ioo 0 (2 * Real.pi), (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - W).det ≠ 0 :=
  RH10.exists_angle_det_ne_zero W
