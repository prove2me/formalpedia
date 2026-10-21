-- Prove2me | solution 1 for LLLFactor.RedBasis.norm_sq_ge_gs_of_last
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:43:31.038357+00:00
-- url     : https://prove2.me/submissions/8b0641f8-b447-46c8-9892-b42446ec26ae

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

theorem lll_last {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b) (r : Fin n → ℤ) (i : Fin n)
    (hri : r i ≠ 0) (hlast : ∀ l, i < l → r l = 0) :
    ‖gs b i‖ ^ 2 ≤ ‖∑ l : Fin n, ((r l : ℤ) : ℝ) • b l‖ ^ 2 := by
  set x : Vec n := ∑ l : Fin n, ((r l : ℤ) : ℝ) • b l with hx
  have hgi : gs b i ≠ 0 := gramSchmidt_ne_zero i hb
  have hpos : 0 < ‖gs b i‖ := norm_pos_iff.mpr hgi
  have hin : inner ℝ x (gs b i) = (r i : ℝ) * ‖gs b i‖ ^ 2 := by
    rw [hx, sum_inner, Finset.sum_eq_single i]
    · rw [real_inner_smul_left]
      congr 1
      rw [lll_b_decomp b i, inner_add_left, sum_inner]
      have : ∑ j ∈ Finset.Iio i, inner ℝ (mu b i j • gs b j) (gs b i) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [real_inner_smul_left, lll_gs_orth b (Finset.mem_Iio.mp hj).ne]; simp
      rw [this, add_zero, real_inner_self_eq_norm_sq]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hli | hli
      · rw [real_inner_smul_left]
        have := gramSchmidt_inv_triangular ℝ b hli
        rw [real_inner_comm] at this
        have h' : inner ℝ (b l) (gs b i) = 0 := by simpa [gs] using this
        rw [h']; simp
      · rw [hlast l hli]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
  have hcs := abs_real_inner_le_norm x (gs b i)
  rw [hin, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖gs b i‖ ^ 2)] at hcs
  have hri1 : (1 : ℝ) ≤ |(r i : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hri
  have h1 : ‖gs b i‖ ≤ ‖x‖ := by
    have : |(r i : ℝ)| * ‖gs b i‖ * ‖gs b i‖ ≤ ‖x‖ * ‖gs b i‖ := by nlinarith [hcs]
    have := le_of_mul_le_mul_right this hpos
    nlinarith
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2


theorem solution {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (r : Fin n → ℤ) (i : Fin n)
  (hri : r i ≠ 0) (hlast : ∀ l, i < l → r l = 0) :
  ‖gs b i‖ ^ 2 ≤ ‖∑ l : Fin n, ((r l : ℤ) : ℝ) • b l‖ ^ 2 :=
  lll_last b hb r i hri hlast
