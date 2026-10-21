-- Prove2me | solution 1 for LLLFactor.RedBasis.gs_sq_le_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:43:27.929977+00:00
-- url     : https://prove2.me/submissions/75c24c49-8b03-43e5-9c6e-e00b7ee934bc

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

theorem lll_pow_mul {n : ℕ} (b : Fin n → Vec n) (hred : IsReduced b) :
    ∀ d : ℕ, ∀ j i : Fin n, (i : ℕ) = j + d → ‖gs b j‖ ^ 2 ≤ (2 : ℝ) ^ d * ‖gs b i‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro j i h
    have : i = j := Fin.ext (by simpa using h)
    subst this; simp
  | succ d ih =>
    intro j i h
    have hlt : (j : ℕ) + d + 1 < n := by have := i.2; omega
    have h1 := ih j ⟨(j : ℕ) + d, by omega⟩ rfl
    have h2 := (lll_half b hred ((j : ℕ) + d) (by omega))
    have h3 : ‖gs b ⟨(j : ℕ) + d, by omega⟩‖ ^ 2 ≤ 2 * ‖gs b i‖ ^ 2 := by
      have hi' : i = ⟨(j : ℕ) + d + 1, hlt⟩ := Fin.ext (by simp; omega)
      subst hi'
      linarith [h2.1, h2.2]
    calc ‖gs b j‖ ^ 2 ≤ 2 ^ d * ‖gs b ⟨(j : ℕ) + d, by omega⟩‖ ^ 2 := h1
      _ ≤ 2 ^ d * (2 * ‖gs b i‖ ^ 2) := by gcongr
      _ = 2 ^ (d + 1) * ‖gs b i‖ ^ 2 := by ring

theorem lll_pow_mul' {n : ℕ} (b : Fin n → Vec n) (hred : IsReduced b) (i j : Fin n) (h : j ≤ i) :
    ‖gs b j‖ ^ 2 ≤ (2 : ℝ) ^ ((i : ℕ) - (j : ℕ)) * ‖gs b i‖ ^ 2 :=
  lll_pow_mul b hred ((i : ℕ) - (j : ℕ)) j i (by have := Fin.le_def.mp h; omega)

theorem lll_geo : ∀ m : ℕ, ∑ k ∈ Finset.range m, (2 : ℝ) ^ (m - k) = 2 ^ (m + 1) - 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : ∑ k ∈ Finset.range m, (2 : ℝ) ^ (m + 1 - k) = 2 * ∑ k ∈ Finset.range m, (2 : ℝ) ^ (m - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ m := (Finset.mem_range.mp hk).le
      rw [show m + 1 - k = (m - k) + 1 by omega]; ring
    rw [this, ih]
    simp
    ring

theorem lll_norm_sq_le {n : ℕ} (b : Fin n → Vec n) (hred : IsReduced b) (i : Fin n) :
    ‖b i‖ ^ 2 ≤ (2 : ℝ) ^ (i : ℕ) * ‖gs b i‖ ^ 2 := by
  rw [lll_norm_decomp]
  have hmu : ∀ j ∈ Finset.Iio i, mu b i j ^ 2 * ‖gs b j‖ ^ 2 ≤
      (1 / 4) * (2 ^ ((i : ℕ) - (j : ℕ)) * ‖gs b i‖ ^ 2) := by
    intro j hj
    have hj' : j < i := Finset.mem_Iio.mp hj
    have h1 := hred.1 i j hj'
    have h2 : mu b i j ^ 2 ≤ 1 / 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      linarith
    have h3 := lll_pow_mul' b hred i j hj'.le
    calc mu b i j ^ 2 * ‖gs b j‖ ^ 2 ≤ (1 / 4) * ‖gs b j‖ ^ 2 := by gcongr
      _ ≤ (1 / 4) * (2 ^ ((i : ℕ) - (j : ℕ)) * ‖gs b i‖ ^ 2) := by gcongr
  have hsum := Finset.sum_le_sum hmu
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hgeo : ∑ j ∈ Finset.Iio i, (2 : ℝ) ^ ((i : ℕ) - (j : ℕ)) = 2 ^ ((i : ℕ) + 1) - 2 := by
    have : ∑ j ∈ Finset.Iio i, (2 : ℝ) ^ ((i : ℕ) - (j : ℕ)) =
        ∑ k ∈ Finset.range (i : ℕ), (2 : ℝ) ^ ((i : ℕ) - k) := by
      have e1 : ∑ j ∈ Finset.Iio i, (2 : ℝ) ^ ((i : ℕ) - (j : ℕ)) =
          ∑ k ∈ (Finset.Iio i).map Fin.valEmbedding, (2 : ℝ) ^ ((i : ℕ) - k) := by
        rw [Finset.sum_map]; rfl
      rw [e1, Fin.map_valEmbedding_Iio, Nat.Iio_eq_range]
    rw [this, lll_geo]
  rw [hgeo] at hsum
  have hx : (1 : ℝ) ≤ 2 ^ (i : ℕ) := one_le_pow₀ (by norm_num)
  have hnn : 0 ≤ ‖gs b i‖ ^ 2 := by positivity
  have : (2 : ℝ) ^ ((i : ℕ) + 1) = 2 * 2 ^ (i : ℕ) := by ring
  rw [this] at hsum
  nlinarith


theorem solution {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (hred : IsReduced b) :
  ∀ i j : Fin n, j ≤ i → ‖gs b j‖ ^ 2 ≤
    (2 : ℝ) ^ ((i : ℕ) - (j : ℕ)) * ‖gs b i‖ ^ 2 := by
  intro i j h
  exact lll_pow_mul' b hred i j h
