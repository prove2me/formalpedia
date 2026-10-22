-- Prove2me | solution 1 for NatureSLT.Kernels.christoffel_darboux
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:35:38.581222+00:00
-- url     : https://prove2.me/submissions/1640bee4-b2de-4e49-b1fc-f68c7a66c372

import Mathlib

open MeasureTheory
open Polynomial in
theorem g70slt_polyint (μ : Measure ℝ) (hmom : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) μ)
    (p : ℝ[X]) : Integrable (fun x => p.eval x) μ := by
  have : (fun x => p.eval x) = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
    funext x; exact eval_eq_sum_range x
  rw [this]; exact integrable_finset_sum _ (fun i _ => (hmom i).const_mul _)

open Polynomial in
noncomputable def g70slt_ip (μ : Measure ℝ) (p q : ℝ[X]) : ℝ := ∫ x, (p * q).eval x ∂μ

open Polynomial in
theorem g70slt_ip_sum (μ : Measure ℝ) (hmom : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) μ)
    (P : ℕ → ℝ[X]) (s : Finset ℕ) (d : ℕ → ℝ) (q : ℝ[X]) :
    g70slt_ip μ (∑ j ∈ s, C (d j) * P j) q = ∑ j ∈ s, d j * g70slt_ip μ (P j) q := by
  unfold g70slt_ip
  rw [Finset.sum_mul]
  simp only [eval_finset_sum]
  rw [integral_finset_sum _ (fun j _ => g70slt_polyint μ hmom _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← integral_const_mul]
  congr 1; funext x; simp [mul_assoc]

open Polynomial in
theorem g70slt_span (μ : Measure ℝ) (n : ℕ) (P : ℕ → ℝ[X])
    (hdeg : ∀ k ∈ Finset.Icc 1 (n + 1), (P k).natDegree = k - 1)
    (hP1 : P 1 ≠ 0) :
    ∀ m, m ≤ n → ∀ q : ℝ[X], q.natDegree ≤ m →
      ∃ d : ℕ → ℝ, q = ∑ j ∈ Finset.Icc 1 (m + 1), C (d j) * P j := by
  intro m
  induction m with
  | zero =>
    intro _ q hq
    have h1 : (P 1).natDegree = 0 := by simpa using hdeg 1 (by simp)
    have e1 := eq_C_of_natDegree_eq_zero h1
    set p0 := (P 1).coeff 0 with hp0
    have hc : p0 ≠ 0 := by
      intro h; apply hP1; rw [e1, h, C_0]
    have hqC := eq_C_of_natDegree_le_zero hq
    set c0 := q.coeff 0 with hc0
    refine ⟨fun _ => c0 / p0, ?_⟩
    rw [Finset.Icc_self, Finset.sum_singleton, e1, ← C_mul, div_mul_cancel₀ _ hc]
    exact hqC
  | succ m ih =>
    intro hm q hq
    have hdm : (P (m + 2)).natDegree = m + 1 := by
      have := hdeg (m + 2) (by simp [Finset.mem_Icc]; omega); simpa using this
    have hP0 : P (m + 2) ≠ 0 := by
      intro h; rw [h] at hdm; simp at hdm
    have hlc : (P (m + 2)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    set c := q.coeff (m + 1) / (P (m + 2)).leadingCoeff with hcdef
    set q' := q - C c * P (m + 2) with hq'
    have hq'1 : q'.natDegree ≤ m + 1 := by
      refine (natDegree_sub_le _ _).trans (max_le hq ?_)
      exact (natDegree_C_mul_le _ _).trans hdm.le
    have hq'c : q'.coeff (m + 1) = 0 := by
      have hcoef : (P (m + 2)).coeff (m + 1) = (P (m + 2)).leadingCoeff := by
        rw [leadingCoeff, hdm]
      rw [hq', coeff_sub, coeff_C_mul, hcoef, hcdef, div_mul_cancel₀ _ hlc, sub_self]
    have hq'2 : q'.natDegree ≤ m := by
      by_contra h
      have e : q'.natDegree = m + 1 := by omega
      have : q'.leadingCoeff = 0 := by rw [leadingCoeff, e]; exact hq'c
      rw [leadingCoeff_eq_zero] at this
      rw [this] at e; simp at e
    obtain ⟨d', hd'⟩ := ih (by omega) q' hq'2
    refine ⟨fun j => if j = m + 2 then c else d' j, ?_⟩
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : ∑ j ∈ Finset.Icc 1 (m + 1), C (if j = m + 2 then c else d' j) * P j =
        ∑ j ∈ Finset.Icc 1 (m + 1), C (d' j) * P j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [if_neg]; simp [Finset.mem_Icc] at hj; omega
    rw [this, ← hd', hq']
    beta_reduce
    rw [if_pos (by omega)]
    ring

open Polynomial in
theorem g70slt_expand (μ : Measure ℝ) (hmom : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) μ)
    (n : ℕ) (P : ℕ → ℝ[X])
    (hdeg : ∀ k ∈ Finset.Icc 1 (n + 1), (P k).natDegree = k - 1)
    (horth : ∀ i ∈ Finset.Icc 1 (n + 1), ∀ j ∈ Finset.Icc 1 (n + 1),
      ∫ x, (P i).eval x * (P j).eval x ∂μ = if i = j then 1 else 0)
    (m : ℕ) (hm : m ≤ n) (q : ℝ[X]) (hq : q.natDegree ≤ m) :
    q = ∑ j ∈ Finset.Icc 1 (m + 1), C (g70slt_ip μ q (P j)) * P j := by
  have hP1 : P 1 ≠ 0 := by
    intro h
    have := horth 1 (by simp) 1 (by simp)
    simp [h] at this
  obtain ⟨d, hd⟩ := g70slt_span μ n P hdeg hP1 m hm q hq
  have key : ∀ i ∈ Finset.Icc 1 (m + 1), g70slt_ip μ q (P i) = d i := by
    intro i hi
    conv_lhs => rw [hd]
    rw [g70slt_ip_sum μ hmom]
    have hi' : i ∈ Finset.Icc 1 (n + 1) := by simp [Finset.mem_Icc] at hi ⊢; omega
    rw [Finset.sum_eq_single_of_mem i hi]
    · have := horth i hi' i hi'
      simp only [g70slt_ip, eval_mul, this, if_true, mul_one]
    · intro j hj hji
      have hj' : j ∈ Finset.Icc 1 (n + 1) := by simp [Finset.mem_Icc] at hj ⊢; omega
      have := horth j hj' i hi'
      simp only [g70slt_ip, eval_mul, this, if_neg hji, mul_zero]
  conv_lhs => rw [hd]
  exact Finset.sum_congr rfl (fun j hj => by rw [key j hj])


/-- Eq. (6.21) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.3.1, p. 192),
the Christoffel–Darboux formula. `P₁, P₂, …` are orthonormal polynomials with respect to a
measure `μ` on `ℝ` with finite moments of every order; `P_k` has degree `k - 1` (the basis
`P₁, …, P_n` has `n` elements, the first being the constant), and orthonormality is required
for `P₁, …, P_{n+1}`. Then there is a constant `a_n` (depending on the family and on `n`) with
`K_n(x, y) = Σ_{k=1}^n P_k(x) P_k(y) = a_n (P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y)) / (x - y)`
for `x ≠ y`, and
`K_n(x, x) = Σ_{k=1}^n P_k(x)² = a_n [P'_{n+1}(x) P_n(x) - P'_n(x) P_{n+1}(x)]`. -/
theorem solution (μ : Measure ℝ) (hmom : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) μ)
    (n : ℕ) (P : ℕ → Polynomial ℝ)
    (hdeg : ∀ k ∈ Finset.Icc 1 (n + 1), (P k).natDegree = k - 1)
    (horth : ∀ i ∈ Finset.Icc 1 (n + 1), ∀ j ∈ Finset.Icc 1 (n + 1),
      ∫ x, (P i).eval x * (P j).eval x ∂μ = if i = j then 1 else 0) :
    ∃ a : ℝ,
      (∀ x y : ℝ, x ≠ y →
        ∑ k ∈ Finset.Icc 1 n, (P k).eval x * (P k).eval y =
          a * ((P (n + 1)).eval x * (P n).eval y - (P n).eval x * (P (n + 1)).eval y) / (x - y)) ∧
      ∀ x : ℝ,
        ∑ k ∈ Finset.Icc 1 n, (P k).eval x ^ 2 =
          a * ((P (n + 1)).derivative.eval x * (P n).eval x -
            (P n).derivative.eval x * (P (n + 1)).eval x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨0, fun x y _ => by simp, fun x => by simp⟩
  set J : ℕ → ℕ → ℝ := fun k j => g70slt_ip μ (Polynomial.X * P k) (P j) with hJ
  have hdegX : ∀ k ∈ Finset.Icc 1 n, (Polynomial.X * P k).natDegree ≤ k := by
    intro k hk
    have hk' : k ∈ Finset.Icc 1 (n + 1) := by simp [Finset.mem_Icc] at hk ⊢; omega
    refine (Polynomial.natDegree_mul_le).trans ?_
    have := hdeg k hk'
    have := Polynomial.natDegree_X_le (R := ℝ)
    simp [Finset.mem_Icc] at hk; omega
  have hexp : ∀ k ∈ Finset.Icc 1 n, ∀ x : ℝ,
      x * (P k).eval x = ∑ j ∈ Finset.Icc 1 (n + 1), J k j * (P j).eval x := by
    intro k hk x
    have e := g70slt_expand μ hmom n P hdeg horth n le_rfl _ ((hdegX k hk).trans
      (by simp [Finset.mem_Icc] at hk; omega))
    have := congrArg (Polynomial.eval x) e
    simpa [Polynomial.eval_finset_sum] using this
  have hsym : ∀ k j, J k j = J j k := by
    intro k j; simp only [hJ, g70slt_ip]; congr 1; funext x; simp; ring
  have hvan : ∀ k ∈ Finset.Icc 1 n, k ≠ n → J k (n + 1) = 0 := by
    intro k hk hkn
    have hkn' : k < n := by simp [Finset.mem_Icc] at hk; omega
    have e := g70slt_expand μ hmom n P hdeg horth k hkn'.le _ (hdegX k hk)
    simp only [hJ]
    rw [e, g70slt_ip_sum μ hmom]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hj' : j ∈ Finset.Icc 1 (n + 1) := by simp [Finset.mem_Icc] at hj ⊢; omega
    have := horth j hj' (n + 1) (by simp [Finset.mem_Icc])
    simp only [g70slt_ip, Polynomial.eval_mul, this]
    rw [if_neg (by simp [Finset.mem_Icc] at hj; omega)]; ring
  have hmain : ∀ x y : ℝ, (x - y) * ∑ k ∈ Finset.Icc 1 n, (P k).eval x * (P k).eval y =
      J n (n + 1) * ((P (n + 1)).eval x * (P n).eval y - (P n).eval x * (P (n + 1)).eval y) := by
    intro x y
    have h1 : (x - y) * ∑ k ∈ Finset.Icc 1 n, (P k).eval x * (P k).eval y =
        ∑ k ∈ Finset.Icc 1 n, ((x * (P k).eval x) * (P k).eval y
          - (P k).eval x * (y * (P k).eval y)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
    rw [h1]
    have h2 : ∀ k ∈ Finset.Icc 1 n, ((x * (P k).eval x) * (P k).eval y
          - (P k).eval x * (y * (P k).eval y)) =
        ∑ j ∈ Finset.Icc 1 n, J k j * ((P j).eval x * (P k).eval y - (P k).eval x * (P j).eval y)
        + J k (n + 1) * ((P (n + 1)).eval x * (P k).eval y - (P k).eval x * (P (n + 1)).eval y) := by
      intro k hk
      rw [hexp k hk x, hexp k hk y, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have e3 : ∑ j ∈ Finset.Icc 1 n, J k j * ((P j).eval x * (P k).eval y - (P k).eval x * (P j).eval y)
          = (∑ j ∈ Finset.Icc 1 n, J k j * (P j).eval x) * (P k).eval y
            - (P k).eval x * (∑ j ∈ Finset.Icc 1 n, J k j * (P j).eval y) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e3]; ring
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
    have hS : ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
        J k j * ((P j).eval x * (P k).eval y - (P k).eval x * (P j).eval y) = 0 := by
      have hneg : ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
          J k j * ((P j).eval x * (P k).eval y - (P k).eval x * (P j).eval y) =
          - ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
          J k j * ((P j).eval x * (P k).eval y - (P k).eval x * (P j).eval y) := by
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hsym j k]; ring
      linarith
    rw [hS, zero_add, Finset.sum_eq_single_of_mem n (by simp [Finset.mem_Icc]; omega)]
    intro k hk hkn
    rw [hvan k hk hkn, zero_mul]
  refine ⟨J n (n + 1), fun x y hxy => ?_, fun y => ?_⟩
  · rw [eq_div_iff (sub_ne_zero.mpr hxy), mul_comm, hmain x y]
  · -- polynomial identity in X for fixed y
    set L : Polynomial ℝ := (Polynomial.X - Polynomial.C y) *
      ∑ k ∈ Finset.Icc 1 n, P k * Polynomial.C ((P k).eval y) with hL
    set R : Polynomial ℝ := Polynomial.C (J n (n + 1)) *
      (P (n + 1) * Polynomial.C ((P n).eval y) - P n * Polynomial.C ((P (n + 1)).eval y)) with hR
    have hLR : L = R := by
      apply Polynomial.funext; intro x
      simp only [hL, hR, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_finset_sum]
      exact hmain x y
    have hd := congrArg (fun p => (Polynomial.derivative p).eval y) hLR
    simp only [hL, hR, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_finset_sum, Polynomial.derivative_sum, sub_self, zero_mul, mul_zero,
      add_zero, sub_zero, one_mul, zero_add] at hd
    rw [← hd]
    refine Finset.sum_congr rfl (fun k _ => by ring)

