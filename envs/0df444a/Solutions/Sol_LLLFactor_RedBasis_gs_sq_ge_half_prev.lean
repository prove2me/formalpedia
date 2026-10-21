-- Prove2me | solution 1 for LLLFactor.RedBasis.gs_sq_ge_half_prev
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:43:26.848763+00:00
-- url     : https://prove2.me/submissions/a2ddbf6f-fa2d-4cf2-8fb5-91c18dd728c1

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

set_option autoImplicit false

open LLLFactor.RedBasis InnerProductSpace

theorem lll_b_decomp {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    b i = gs b i + ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
  refine (gramSchmidt_def'' ℝ b i).trans ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  unfold mu gs
  rw [real_inner_comm, real_inner_self_eq_norm_sq]
  rfl

theorem lll_gs_orth {n : ℕ} (b : Fin n → Vec n) {i j : Fin n} (h : i ≠ j) :
    inner ℝ (gs b i) (gs b j) = 0 := gramSchmidt_orthogonal ℝ b h

theorem lll_norm_sum {n : ℕ} (b : Fin n → Vec n) (S : Finset (Fin n)) (c : Fin n → ℝ) :
    ‖∑ j ∈ S, c j • gs b j‖ ^ 2 = ∑ j ∈ S, c j ^ 2 * ‖gs b j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  · intro k _ hkj
    rw [real_inner_smul_left, real_inner_smul_right, lll_gs_orth b (Ne.symm hkj)]; simp
  · intro h; exact absurd hj h

theorem lll_norm_decomp {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    ‖b i‖ ^ 2 = ‖gs b i‖ ^ 2 + ∑ j ∈ Finset.Iio i, mu b i j ^ 2 * ‖gs b j‖ ^ 2 := by
  have h0 : inner ℝ (gs b i) (∑ j ∈ Finset.Iio i, mu b i j • gs b j) = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : i ≠ j := (Finset.mem_Iio.mp hj).ne'
    rw [real_inner_smul_right, lll_gs_orth b this]; simp
  conv_lhs => rw [lll_b_decomp b i]
  rw [norm_add_sq_real, h0, lll_norm_sum]
  ring

theorem lll_half {n : ℕ} (b : Fin n → Vec n) (hred : IsReduced b) (i : ℕ) (hi : i + 1 < n) :
    (1 / 2 : ℝ) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤ ((3 / 4 : ℝ) - mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ∧
    ((3 / 4 : ℝ) - mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤ ‖gs b ⟨i + 1, hi⟩‖ ^ 2 := by
  have h1 := hred.2 i hi
  have hne : (⟨i + 1, hi⟩ : Fin n) ≠ ⟨i, by omega⟩ := by simp [Fin.ext_iff]
  have e : ‖gs b ⟨i + 1, hi⟩ + mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ • gs b ⟨i, by omega⟩‖ ^ 2
      = ‖gs b ⟨i + 1, hi⟩‖ ^ 2 + mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2 * ‖gs b ⟨i, by omega⟩‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, lll_gs_orth b hne, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  have hmu := hred.1 ⟨i + 1, hi⟩ ⟨i, by omega⟩ (by simp [Fin.lt_def])
  have hmu2 : mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hmu 2
    rw [sq_abs] at this
    linarith
  have hnn : 0 ≤ ‖gs b ⟨i, by omega⟩‖ ^ 2 := by positivity
  constructor
  · nlinarith
  · rw [e] at h1
    nlinarith


theorem solution {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (hred : IsReduced b) :
  ∀ (i : ℕ) (hi : i + 1 < n),
    ((3 / 4 : ℝ) - mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤
        ‖gs b ⟨i + 1, hi⟩‖ ^ 2 ∧
      (1 / 2 : ℝ) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤
        ((3 / 4 : ℝ) - mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2) * ‖gs b ⟨i, by omega⟩‖ ^ 2 := by
  intro i hi
  exact ⟨(lll_half b hred i hi).2, (lll_half b hred i hi).1⟩
