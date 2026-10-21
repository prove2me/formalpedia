-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.monic_relations_of_bounded_representatives
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:41:09.831628+00:00
-- url     : https://prove2.me/submissions/badc09c5-8082-418a-838b-38376d382bad

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

/-!
# Monic relations from weighted bounded representatives

Given weighted bounded representatives for all positive powers of an ideal `I`
with slope `rho < R` and additive overhead `B`, we construct a common exponent
`k > 0`, positive integers `b i`, elements `F i ∈ I ^ k` and a slope `a < R` such
that `X i ^ (b i) - F i` is supported strictly below the weighted order
`w i * b i`, with pivot weights bounded by `k * a`.

The construction takes `k` with `B + sum w < k * (R - rho)`,
`b i = floor ((k * rho + B) / w i) + 1`, and `F i = X i ^ (b i) - Q i` where
`Q i` is the bounded representative of `X i ^ (b i)`; then
`X i ^ (b i) - F i = Q i` has weighted support at most `k * rho + B < w i * b i`,
and `a = rho + (B + sum w) / k` gives `w i * b i ≤ k * a` with `a < R`.
-/

theorem solution
    {m : ℕ} (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (R rho B : ℝ) (hrho0 : 0 < rho) (hrhoR : rho < R) (hB : 0 ≤ B)
    (hbound : ∀ k : ℕ, 0 < k → ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
        P - Q ∈ I ^ k ∧
        ∀ u ∈ Q.support, ∑ i, w i * (u i : ℝ) ≤ (k : ℝ) * rho + B) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : Fin (m + 1) → ℕ, (∀ i, 0 < b i) ∧
      ∃ F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ, ∃ a : ℝ,
        0 < a ∧ a < R ∧
        (∀ i, F i ∈ I ^ k) ∧
        (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, w j * (u j : ℝ)) < w i * (b i : ℝ)) ∧
        (∀ i, w i * (b i : ℝ) ≤ (k : ℝ) * a) := by

  classical
  -- a nonnegative bound `W` for all the weights
  set W : ℝ := ∑ i, w i with hW
  have hWnonneg : 0 ≤ W := Finset.sum_nonneg (fun i _ => le_of_lt (hw i))
  have hwW : ∀ i, w i ≤ W := fun i =>
    Finset.single_le_sum (fun j _ => le_of_lt (hw j)) (Finset.mem_univ i)
  have hRrho : 0 < R - rho := by linarith
  -- choose the common ideal exponent `k` large enough
  obtain ⟨k, hk, hkbig⟩ : ∃ k : ℕ, 0 < k ∧ B + W < (k : ℝ) * (R - rho) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((B + W) / (R - rho))
    rw [div_lt_iff₀ hRrho] at hn
    refine ⟨max n 1, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right n 1), ?_⟩
    have hnle : (n : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left n 1
    calc B + W < (n : ℝ) * (R - rho) := hn
      _ ≤ ((max n 1 : ℕ) : ℝ) * (R - rho) :=
          mul_le_mul_of_nonneg_right hnle (le_of_lt hRrho)
  -- the pivot exponents and the slope
  set b : Fin (m + 1) → ℕ := fun i => Nat.floor (((k : ℝ) * rho + B) / w i) + 1 with hbdef
  have hbpos : ∀ i, 0 < b i := by
    intro i
    simp only [hbdef]
    omega
  set a : ℝ := rho + (B + W) / (k : ℝ) with hadef
  have hak_pos : 0 < a := by
    rw [hadef]
    have : 0 ≤ (B + W) / (k : ℝ) := by positivity
    linarith
  have hak_R : a < R := by
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    rw [hadef,
      show rho + (B + W) / (k : ℝ) = (rho * (k : ℝ) + (B + W)) / (k : ℝ) by
        field_simp]
    rw [div_lt_iff₀ hkpos]
    nlinarith
  -- the polynomials `F i`
  set F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ := fun i =>
    MvPolynomial.X i ^ b i - (hbound k hk (MvPolynomial.X i ^ b i)).choose with hFdef
  have hFmem : ∀ i, F i ∈ I ^ k := by
    intro i
    have := (hbound k hk (MvPolynomial.X i ^ b i)).choose_spec.1
    simpa only [hFdef] using this
  have hFsupp : ∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, w j * (u j : ℝ)) < w i * (b i : ℝ) := by
    intro i u hu
    have hQ : MvPolynomial.X i ^ b i - F i =
        (hbound k hk (MvPolynomial.X i ^ b i)).choose := by
      rw [hFdef]
      ring
    rw [hQ] at hu
    have hle := (hbound k hk (MvPolynomial.X i ^ b i)).choose_spec.2 u hu
    have hlt : (k : ℝ) * rho + B < w i * (b i : ℝ) := by
      have h1 : ((k : ℝ) * rho + B) / w i < (Nat.floor (((k : ℝ) * rho + B) / w i) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      rw [div_lt_iff₀ (hw i)] at h1
      have hb : (b i : ℝ) = (Nat.floor (((k : ℝ) * rho + B) / w i) : ℝ) + 1 := by
        rw [hbdef]
        push_cast
        ring
      rw [hb]
      linarith
    linarith
  have hFbudget : ∀ i, w i * (b i : ℝ) ≤ (k : ℝ) * a := by
    intro i
    have hnum : 0 ≤ ((k : ℝ) * rho + B) / w i := by
      apply div_nonneg _ (le_of_lt (hw i))
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      nlinarith
    have hfloor : ((Nat.floor (((k : ℝ) * rho + B) / w i)) : ℝ) ≤ ((k : ℝ) * rho + B) / w i :=
      Nat.floor_le hnum
    rw [le_div_iff₀ (hw i)] at hfloor
    have hb : (b i : ℝ) = (Nat.floor (((k : ℝ) * rho + B) / w i) : ℝ) + 1 := by
      rw [hbdef]
      push_cast
      ring
    rw [hb, hadef]
    have hka : (k : ℝ) * (rho + (B + W) / (k : ℝ)) = (k : ℝ) * rho + (B + W) := by
      field_simp
    rw [hka]
    nlinarith [hwW i]
  exact ⟨k, hk, b, hbpos, F, a, hak_pos, hak_R, hFmem, hFsupp, hFbudget⟩

