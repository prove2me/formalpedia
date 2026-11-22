-- Prove2me | solution 1 for McLeishCLT.MDA.trunc_lintegral_normSq_prodT_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:07:19.18482+00:00
-- url     : https://prove2.me/submissions/98bf4583-f93d-4c28-a18a-005d9fd891a5

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

set_option autoImplicit false

namespace McLeishCLT.MDA.TruncL2Proof

open MeasureTheory Finset

/-- Partial sums of squares are monotone. -/
theorem psum_mono (x : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ range a, x i ^ 2 ≤ ∑ i ∈ range b, x i ^ 2 :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h) fun _ _ _ => sq_nonneg _

/-- The deterministic core: if the partial sums stay `≤ 2` up to index `J` and exceed `2`
strictly after `J` (within the row), the truncated product is at most
`exp(2t²)(1 + t² x_J²)`. -/
theorem prod_le (K : ℕ) (x : ℕ → ℝ) (t : ℝ) (J : ℕ) (hJK : K = 0 ∨ J < K)
    (hle : ∀ j ≤ J, ∑ i ∈ range j, x i ^ 2 ≤ 2)
    (hgt : ∀ j, J < j → j < K → 2 < ∑ i ∈ range j, x i ^ 2) :
    ∏ j ∈ range K, (1 + t ^ 2 * (x j * (if ∑ i ∈ range j, x i ^ 2 ≤ 2 then 1 else 0)) ^ 2)
      ≤ Real.exp (2 * t ^ 2) * (1 + t ^ 2 * x J ^ 2) := by
  have hexp1 : 1 ≤ Real.exp (2 * t ^ 2) := Real.one_le_exp (by positivity)
  have hfac1 : 1 ≤ 1 + t ^ 2 * x J ^ 2 := by nlinarith [sq_nonneg t, sq_nonneg (x J)]
  rcases hJK with hK | hJK
  · subst hK
    simp only [range_zero, prod_empty]
    nlinarith
  rw [← prod_range_mul_prod_Ico _ (Nat.succ_le_of_lt hJK)]
  have htail : ∏ j ∈ Ico (J + 1) K,
      (1 + t ^ 2 * (x j * (if ∑ i ∈ range j, x i ^ 2 ≤ 2 then 1 else 0)) ^ 2) = 1 := by
    refine prod_eq_one fun j hj => ?_
    rw [mem_Ico] at hj
    have h2 := hgt j (by omega) hj.2
    rw [if_neg (not_le.mpr h2)]
    ring
  have hhead : ∀ j ∈ range (J + 1),
      (1 + t ^ 2 * (x j * (if ∑ i ∈ range j, x i ^ 2 ≤ 2 then 1 else 0)) ^ 2)
        = 1 + t ^ 2 * x j ^ 2 := by
    intro j hj
    rw [mem_range] at hj
    rw [if_pos (hle j (by omega))]
    ring
  rw [htail, mul_one, prod_congr rfl hhead, prod_range_succ]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc ∏ j ∈ range J, (1 + t ^ 2 * x j ^ 2)
      ≤ ∏ j ∈ range J, Real.exp (t ^ 2 * x j ^ 2) :=
        prod_le_prod (fun j _ => by positivity) fun j _ => by
          have := Real.add_one_le_exp (t ^ 2 * x j ^ 2)
          linarith
    _ = Real.exp (t ^ 2 * ∑ j ∈ range J, x j ^ 2) := by
        rw [← Real.exp_sum, mul_sum]
    _ ≤ Real.exp (2 * t ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have := hle J le_rfl
        nlinarith [sq_nonneg t]

/-- `stopJ` satisfies the hypotheses of `prod_le`. -/
theorem stopJ_spec {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (k n = 0 ∨ stopJ k X n ω < k n) ∧
    (∀ j ≤ stopJ k X n ω, ∑ i ∈ range j, X n i ω ^ 2 ≤ 2) ∧
    (∀ j, stopJ k X n ω < j → j < k n → 2 < ∑ i ∈ range j, X n i ω ^ 2) := by
  classical
  unfold stopJ
  split_ifs with h
  · -- `J` is the first index whose inclusive partial sum exceeds `2`.
    have hspec := Nat.find_spec h
    refine ⟨Or.inr hspec.1, fun j hj => ?_, fun j hj _ => ?_⟩
    · rcases j with _ | j
      · simp
      · have hmin := Nat.find_min h (show j < Nat.find h by omega)
        push Not at hmin
        exact hmin (by omega)
    · exact lt_of_lt_of_le hspec.2 (psum_mono (fun i => X n i ω) (by omega))
  · push Not at h
    refine ⟨by omega, fun j hj => ?_, fun j hj hjK => by omega⟩
    rcases j with _ | j
    · simp
    · exact h j (by omega)

end McLeishCLT.MDA.TruncL2Proof

open MeasureTheory Finset McLeishCLT.MDA McLeishCLT.MDA.TruncL2Proof

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (t : ℝ) (n : ℕ) :
    ∫⁻ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
        (1 + ENNReal.ofReal (t ^ 2) * ∫⁻ ω, ‖X n (stopJ k X n ω) ω‖ₑ ^ 2 ∂P) := by
  -- Pointwise bound.
  have hpt : ∀ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
        (1 + ENNReal.ofReal (t ^ 2) * ‖X n (stopJ k X n ω) ω‖ₑ ^ 2) := by
    intro ω
    obtain ⟨h1, h2, h3⟩ := stopJ_spec k X n ω
    have hcore := prod_le (k n) (fun i => X n i ω) t (stopJ k X n ω) h1 h2 h3
    have hnorm : ‖prodT k (trunc X) t n ω‖ ^ 2 = ∏ j ∈ range (k n),
        (1 + t ^ 2 * (X n j ω * (if ∑ i ∈ range j, X n i ω ^ 2 ≤ 2 then 1 else 0)) ^ 2) := by
      unfold prodT
      rw [norm_prod, ← prod_pow]
      refine prod_congr rfl fun j _ => ?_
      rw [← Complex.normSq_eq_norm_sq]
      unfold trunc
      push_cast
      rw [Complex.normSq_apply]
      simp
      split_ifs <;> ring
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hnorm,
      Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
      ← ENNReal.ofReal_mul (sq_nonneg t), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (by positivity),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hcore
  calc ∫⁻ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
          (1 + ENNReal.ofReal (t ^ 2) * ‖X n (stopJ k X n ω) ω‖ₑ ^ 2) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
          (1 + ENNReal.ofReal (t ^ 2) * ∫⁻ ω, ‖X n (stopJ k X n ω) ω‖ₑ ^ 2 ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
