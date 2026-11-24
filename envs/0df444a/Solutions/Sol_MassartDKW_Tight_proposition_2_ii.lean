-- Prove2me | solution 1 for MassartDKW.Tight.proposition_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:50:53.104803+00:00
-- url     : https://prove2.me/submissions/cc219067-418b-4620-b2cf-954b0e438e7c

import Mathlib

set_option autoImplicit false

open Finset

/-- `abelL m w = ∑_{j=1}^{m} C(m,j) j^(j-1) (w-j)^(m-j)`, indexed by `k = j - 1`. -/
private noncomputable def abelL (m : ℕ) (w : ℝ) : ℝ :=
  ∑ k ∈ range m, ((m.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ k *
    (w - ((k : ℝ) + 1)) ^ (m - (k + 1))

/-- At `w = 0` the sum is an `m`-th forward difference of `r ↦ r^(m-1)`, hence zero. -/
private lemma abelL_zero (m : ℕ) (hm : 2 ≤ m) : abelL m 0 = 0 := by
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (j := m - 1) (n := m)
    (by omega)) 0
  rw [fwdDiff_iter_eq_sum_shift, sum_range_succ'] at h
  have h0 : (0 : ℝ) ^ (m - 1) = 0 := zero_pow (by omega)
  simp only [Pi.zero_apply, zero_add, zero_smul, h0, smul_zero, add_zero] at h
  rw [abelL]
  refine Eq.trans ?_ h
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  push_cast
  have e : m - 1 = k + (m - (k + 1)) := by omega
  rw [e, pow_add, zero_sub, neg_pow]
  ring

private lemma abelL_hasDerivAt (m : ℕ) (w : ℝ) :
    HasDerivAt (abelL (m + 1)) (((m : ℝ) + 1) * abelL m w) w := by
  have key : ∀ k ∈ range (m + 1), HasDerivAt
      (fun v : ℝ => (((m + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ k *
        (v - ((k : ℝ) + 1)) ^ (m + 1 - (k + 1)))
      ((((m + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ k *
        (((m + 1 - (k + 1) : ℕ) : ℝ) * (w - ((k : ℝ) + 1)) ^ (m + 1 - (k + 1) - 1) * 1)) w := by
    intro k _
    exact (((hasDerivAt_id w).sub_const _).fun_pow _).const_mul _
  have hs := HasDerivAt.fun_sum key
  have hfun : abelL (m + 1) = fun v : ℝ => ∑ k ∈ range (m + 1),
      (((m + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ k *
        (v - ((k : ℝ) + 1)) ^ (m + 1 - (k + 1)) := by
    funext v; rfl
  rw [hfun]
  refine hs.congr_deriv ?_
  rw [sum_range_succ, abelL, mul_sum]
  simp only [Nat.sub_self, CharP.cast_eq_zero, zero_mul, mul_zero, add_zero]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have hc := Nat.choose_mul_succ_eq m (k + 1)
  have hc' : ((m.choose (k + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) =
      (((m + 1).choose (k + 1) : ℕ) : ℝ) * ((m + 1 - (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hc
  have e : m + 1 - (k + 1) - 1 = m - (k + 1) := by omega
  rw [e]
  linear_combination (-1 : ℝ) * ((k : ℝ) + 1) ^ k * (w - ((k : ℝ) + 1)) ^ (m - (k + 1)) * hc'

/-- The Abel-type identity `∑_{j=1}^{m} C(m,j) j^(j-1) (w-j)^(m-j) = m w^(m-1)`. -/
private lemma abelL_eq (m : ℕ) (hm : 1 ≤ m) (w : ℝ) : abelL m w = m * w ^ (m - 1) := by
  induction m, hm using Nat.le_induction generalizing w with
  | base => simp [abelL]
  | succ m hm ih =>
    set g : ℝ → ℝ := fun v => abelL (m + 1) v - ((m + 1 : ℕ) : ℝ) * v ^ (m + 1 - 1)
    have hg : ∀ v, HasDerivAt g 0 v := by
      intro v
      have h1 := abelL_hasDerivAt m v
      have h2 := (hasDerivAt_pow (m + 1 - 1) v).const_mul ((m + 1 : ℕ) : ℝ)
      refine (h1.sub h2).congr_deriv ?_
      rw [ih v]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
    have hconst := is_const_of_deriv_eq_zero (fun v => (hg v).differentiableAt)
      (fun v => (hg v).deriv) w 0
    have hz : g 0 = 0 := by
      simp only [g]
      rw [abelL_zero (m + 1) (by omega), zero_pow (by omega)]
      ring
    have := hconst.trans hz
    simp only [g] at this
    linarith

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n - 1),
      (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j) * ((n : ℝ) ^ n)⁻¹ * (n.choose j) ≤ 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  -- the full sum over `j ∈ [1, n]` equals `n^n`
  have hfull : ∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℕ) : ℝ) * (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j) = (n : ℝ) ^ n := by
    have h := abelL_eq n (by omega) n
    have e : (n : ℝ) * (n : ℝ) ^ (n - 1) = (n : ℝ) ^ n := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at h
    have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [← h, abelL, hI, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply sum_congr rfl
    intro k _
    push_cast
    rw [add_comm 1 k, Nat.add_sub_cancel, add_comm (1 : ℝ)]
  have hsub : ∑ j ∈ Finset.Icc 1 (n - 1),
      ((n.choose j : ℕ) : ℝ) * (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j) ≤
      ∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℕ) : ℝ) * (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j) := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_right (by omega)
    · intro j hj _
      rw [Finset.mem_Icc] at hj
      have : (0 : ℝ) ≤ (n : ℝ) - j := by
        rw [sub_nonneg]; exact_mod_cast hj.2
      positivity
  rw [hfull] at hsub
  calc ∑ j ∈ Finset.Icc 1 (n - 1),
        (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j) * ((n : ℝ) ^ n)⁻¹ * (n.choose j)
      = (∑ j ∈ Finset.Icc 1 (n - 1),
          ((n.choose j : ℕ) : ℝ) * (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j)) *
          ((n : ℝ) ^ n)⁻¹ := by
        rw [sum_mul]; apply sum_congr rfl; intro j _; ring
    _ ≤ (n : ℝ) ^ n * ((n : ℝ) ^ n)⁻¹ := by
        apply mul_le_mul_of_nonneg_right hsub (by positivity)
    _ = 1 := mul_inv_cancel₀ hnpos.ne'
