-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_generic_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:14:14.344811+00:00
-- url     : https://prove2.me/submissions/2fe29c9a-1ee4-4c07-a7bf-68ba1960d0d3

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open scoped BigOperators

private lemma coefficient_control_geometric_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ k := by
  have h : ∀ n : ℕ, (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) + 1 = (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith
  linarith [h k]

-- Multiplication by one bounded factor with zero constant coefficient
-- preserves the bound 2^k, independently of the number of earlier factors.
private lemma coefficient_control_mul_norm
    (g f : PowerSeries ℂ)
    (hg : ∀ k, ‖PowerSeries.coeff k g‖ ≤ (2 : ℝ) ^ k)
    (hf0 : PowerSeries.coeff 0 f = 0)
    (hf : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) (k : ℕ) :
    ‖PowerSeries.coeff k (g * f)‖ ≤ (2 : ℝ) ^ k := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  simp only [Nat.sub_self, hf0, mul_zero, add_zero]
  calc
    ‖∑ j ∈ Finset.range k,
        PowerSeries.coeff j g * PowerSeries.coeff (k - j) f‖
        ≤ ∑ j ∈ Finset.range k,
          ‖PowerSeries.coeff j g * PowerSeries.coeff (k - j) f‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      calc
        ‖PowerSeries.coeff j g‖ * ‖PowerSeries.coeff (k - j) f‖
            ≤ ‖PowerSeries.coeff j g‖ * 1 :=
          mul_le_mul_of_nonneg_left (hf (k - j)) (norm_nonneg _)
        _ ≤ (2 : ℝ) ^ j := by simpa only [mul_one] using hg j
    _ ≤ (2 : ℝ) ^ k := coefficient_control_geometric_sum k

private lemma coefficient_control_pow_mul_norm
    (f g : PowerSeries ℂ)
    (hf0 : PowerSeries.coeff 0 f = 0)
    (hf : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1)
    (hg : ∀ k, ‖PowerSeries.coeff k g‖ ≤ (2 : ℝ) ^ k) (b : ℕ) :
    ∀ k, ‖PowerSeries.coeff k (f ^ b * g)‖ ≤ (2 : ℝ) ^ k := by
  induction b with
  | zero => simpa only [pow_zero, one_mul] using hg
  | succ b ih =>
    intro k
    rw [pow_succ, mul_right_comm]
    exact coefficient_control_mul_norm (f ^ b * g) f ih hf0 hf k

-- Vanishing below prescribed degrees is additive under multiplication.
private lemma coefficient_control_mul_support
    (f g : PowerSeries ℂ) (a b : ℕ)
    (hf : ∀ n, n < a → PowerSeries.coeff n f = 0)
    (hg : ∀ n, n < b → PowerSeries.coeff n g = 0)
    (n : ℕ) (hn : n < a + b) : PowerSeries.coeff n (f * g) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hs : i + j = n := Finset.mem_antidiagonal.mp hij
  by_cases hi : i < a
  · rw [hf i hi, zero_mul]
  · have hj : j < b := by omega
    rw [hg j hj, mul_zero]

private lemma coefficient_control_pow_support
    (f : PowerSeries ℂ) (T : ℕ)
    (hf : ∀ n, n < T → PowerSeries.coeff n f = 0) (b : ℕ) :
    ∀ n, n < T * b → PowerSeries.coeff n (f ^ b) = 0 := by
  induction b with
  | zero =>
    intro n hn
    simp only [Nat.mul_zero] at hn
    omega
  | succ b ih =>
    intro n hn
    rw [pow_succ]
    apply coefficient_control_mul_support (f ^ b) f (T * b) T ih hf n
    simpa only [Nat.mul_succ] using hn

theorem solution
    {m : ℕ} (f : Fin m → PowerSeries ℂ) (T b : Fin m → ℕ) (k : ℕ)
    (hT : ∀ i, 1 ≤ T i)
    (hsupp : ∀ i n, n < T i → PowerSeries.coeff n (f i) = 0)
    (hcoeff : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i : Fin m, (f i) ^ b i)‖ ≤ (2 : ℝ) ^ k ∧
    (PowerSeries.coeff k (∏ i : Fin m, (f i) ^ b i) ≠ 0 →
      ∑ i : Fin m, T i * b i ≤ k) := by
  classical
  have hnorm : ∀ s : Finset (Fin m), ∀ n,
      ‖PowerSeries.coeff n (∏ i ∈ s, (f i) ^ b i)‖ ≤ (2 : ℝ) ^ n := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro n
      simp only [Finset.prod_empty, PowerSeries.coeff_one]
      by_cases hn : n = 0
      · subst n
        norm_num
      · rw [if_neg hn]
        simpa only [norm_zero] using
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    | @insert i s hi ih =>
      intro n
      rw [Finset.prod_insert hi]
      apply coefficient_control_pow_mul_norm (f i) (∏ j ∈ s, (f j) ^ b j)
        (hsupp i 0 (by have ht := hT i; omega)) (hcoeff i) ih (b i) n
  have hsupport : ∀ s : Finset (Fin m), ∀ n,
      n < ∑ i ∈ s, T i * b i →
        PowerSeries.coeff n (∏ i ∈ s, (f i) ^ b i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro n hn
      simp only [Finset.sum_empty] at hn
      omega
    | @insert i s hi ih =>
      intro n hn
      rw [Finset.prod_insert hi]
      apply coefficient_control_mul_support ((f i) ^ b i) (∏ j ∈ s, (f j) ^ b j)
        (T i * b i) (∑ j ∈ s, T j * b j)
        (coefficient_control_pow_support (f i) (T i) (hsupp i) (b i)) ih n
      simpa only [Finset.sum_insert hi] using hn
  refine ⟨hnorm Finset.univ k, ?_⟩
  intro hk
  by_contra h
  exact hk (hsupport Finset.univ k (Nat.lt_of_not_ge h))
