-- Prove2me | solution 1 for NeuralCollapseCE.ce_quadratic_form_bound
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:18:50.879252+00:00
-- url     : https://prove2.me/submissions/b58ea9a9-be66-476d-bfb4-bd4e6a752043

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic
set_option autoImplicit false
open MeasureTheory Filter Topology Asymptotics
open NeuralCollapseCE

/-- Key identity: `∑ ‖n (v_i - u_i) + U‖² + n ‖U‖² = 2n (n² - Q)`. -/
private lemma qf_identity {n d : ℕ} (u v : Fin n → Vec d)
    (hu : IsUnitConfig u) (hv : IsUnitConfig v) :
    ∑ i, ‖(n : ℝ) • (v i - u i) + ∑ j, u j‖ ^ 2 + (n : ℝ) * ‖∑ j, u j‖ ^ 2 =
      2 * (n : ℝ) * ((n : ℝ) ^ 2 -
        ((n : ℝ) * ∑ i, inner ℝ (v i) (u i) - inner ℝ (∑ i, v i) (∑ i, u i))) := by
  set U := ∑ j, u j with hU
  have h1 : ∀ i, ‖(n : ℝ) • (v i - u i) + U‖ ^ 2 =
      (n : ℝ) ^ 2 * (2 - 2 * inner ℝ (v i) (u i)) +
        2 * (n : ℝ) * (inner ℝ (v i) U - inner ℝ (u i) U) + ‖U‖ ^ 2 := by
    intro i
    rw [norm_add_sq_real, norm_smul, mul_pow, norm_sub_sq_real, hu i, hv i, inner_smul_left,
      inner_sub_left]
    simp only [Real.norm_eq_abs, sq_abs, conj_trivial, one_pow]
    ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← sum_inner, ← sum_inner,
    ← hU, real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem solution {n d : ℕ} (u v : Fin n → Vec d)
    (hu : IsUnitConfig u) (hv : IsUnitConfig v) :
    (n : ℝ) * ∑ i, inner ℝ (v i) (u i) - inner ℝ (∑ i, v i) (∑ i, u i) ≤ (n : ℝ) ^ 2 ∧
      ((n : ℝ) * ∑ i, inner ℝ (v i) (u i) - inner ℝ (∑ i, v i) (∑ i, u i) = (n : ℝ) ^ 2 ↔
        (∑ i, u i = 0 ∧ v = u)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by simp, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, CharP.cast_eq_zero, inner_zero_left,
      mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, true_and,
      true_iff]
    funext i; exact i.elim0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid := qf_identity u v hu hv
  set Q := (n : ℝ) * ∑ i, inner ℝ (v i) (u i) - inner ℝ (∑ i, v i) (∑ i, u i) with hQ
  set U := ∑ j, u j with hU
  have hS : 0 ≤ ∑ i, ‖(n : ℝ) • (v i - u i) + U‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hUn : 0 ≤ ‖U‖ ^ 2 := sq_nonneg _
  refine ⟨?_, ?_⟩
  · by_contra h
    nlinarith [mul_nonneg hn'.le hUn]
  constructor
  · intro hq
    rw [hq, sub_self, mul_zero] at hid
    have hUz : ‖U‖ ^ 2 = 0 := by nlinarith [mul_nonneg hn'.le hUn]
    have hSz : ∑ i, ‖(n : ℝ) • (v i - u i) + U‖ ^ 2 = 0 := by nlinarith [mul_nonneg hn'.le hUn]
    have hU0 : U = 0 := by simpa using hUz
    refine ⟨hU0, ?_⟩
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg
      ‖(n : ℝ) • (v i - u i) + U‖)).1 hSz i (Finset.mem_univ i)
    rw [hU0, add_zero, sq_eq_zero_iff, norm_eq_zero, smul_eq_zero] at hi
    rcases hi with h | h
    · exact absurd h hn'.ne'
    · exact sub_eq_zero.1 h
  · rintro ⟨hU0, rfl⟩
    rw [hQ, ← hU, hU0, inner_zero_left, sub_zero]
    simp only [real_inner_self_eq_norm_sq, hv _, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
