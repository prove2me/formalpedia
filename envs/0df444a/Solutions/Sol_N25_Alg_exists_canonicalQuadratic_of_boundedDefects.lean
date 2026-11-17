-- Prove2me | solution 1 for N25.Alg.exists_canonicalQuadratic_of_boundedDefects
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:59.212543+00:00
-- url     : https://prove2.me/submissions/cf098929-fb27-4621-bb85-6541089e0a08

import Mathlib

open Filter Topology

namespace N25.Alg

/-- Bounded doubling and parallelogram errors yield a nonnegative quadratic height
at uniformly bounded distance, with the same finiteness of bounded sublevel sets. -/
theorem _root_.solution {G : Type*} [AddCommGroup G] (h₀ : G → ℝ)
    (hnn : ∀ x, 0 ≤ h₀ x) (hN : ∀ B : ℝ, {x | h₀ x ≤ B}.Finite) (C₂ Cp : ℝ)
    (hd : ∀ x, |h₀ (x + x) - 4 * h₀ x| ≤ C₂)
    (hp : ∀ x y, |h₀ (x + y) + h₀ (x - y) - 2 * h₀ x - 2 * h₀ y| ≤ Cp) :
    ∃ q : G → ℝ, (∀ x, 0 ≤ q x) ∧ (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) ∧
      (∀ x, |q x - h₀ x| ≤ C₂ / 3) ∧ ∀ B : ℝ, {x | q x ≤ B}.Finite := by
  classical
  let a : G → ℕ → ℝ := fun x n => (1 / 4 : ℝ) ^ n * h₀ ((2 ^ n : ℕ) • x)
  have hstep (x : G) (n : ℕ) :
      dist (a x n) (a x (n + 1)) ≤ (C₂ / 4) * (1 / 4 : ℝ) ^ n := by
    have hscale : (2 ^ (n + 1) : ℕ) • x = (2 ^ n : ℕ) • x + (2 ^ n : ℕ) • x := by
      rw [pow_succ, mul_nsmul, two_nsmul]
    have heq : a x n - a x (n + 1) =
        -((1 / 4 : ℝ) ^ n / 4) *
          (h₀ (((2 ^ n : ℕ) • x) + (2 ^ n : ℕ) • x) - 4 * h₀ ((2 ^ n : ℕ) • x)) := by
      dsimp only [a]
      rw [hscale, pow_succ]
      ring
    rw [Real.dist_eq, heq, abs_mul, abs_neg,
      abs_of_nonneg (div_nonneg (pow_nonneg (by norm_num) n) (by norm_num))]
    have := mul_le_mul_of_nonneg_left (hd ((2 ^ n : ℕ) • x))
      (div_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n) (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith
  have hconv (x : G) : ∃ v : ℝ, Tendsto (a x) atTop (𝓝 v) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (1 / 4) (C₂ / 4) (by norm_num) (hstep x))
  choose q hq using hconv
  have hclose (x : G) : |q x - h₀ x| ≤ C₂ / 3 := by
    have h := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (C₂ / 4) (by norm_num) (hstep x) (hq x)
    norm_num [a, Real.dist_eq, abs_sub_comm] at h
    calc
      |q x - h₀ x| = |h₀ x - q x| := abs_sub_comm _ _
      _ ≤ C₂ / 4 / (3 / 4) := h
      _ = C₂ / 3 := by ring
  refine ⟨q, ?_, ?_, hclose, ?_⟩
  · intro x
    exact ge_of_tendsto' (hq x) (fun n => mul_nonneg (pow_nonneg (by norm_num) n) (hnn _))
  · intro x y
    have hlim := (((hq (x + y)).add (hq (x - y))).sub
      (((hq x).const_mul 2).add ((hq y).const_mul 2)))
    have hpow : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n * Cp) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).mul_const Cp
    have hzero : Tendsto (fun n => a (x + y) n + a (x - y) n -
        (2 * a x n + 2 * a y n)) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ hpow
      intro n
      have heq : a (x + y) n + a (x - y) n - (2 * a x n + 2 * a y n) =
          (1 / 4 : ℝ) ^ n *
            (h₀ (((2 ^ n : ℕ) • x) + (2 ^ n : ℕ) • y) +
             h₀ (((2 ^ n : ℕ) • x) - (2 ^ n : ℕ) • y) -
             2 * h₀ ((2 ^ n : ℕ) • x) - 2 * h₀ ((2 ^ n : ℕ) • y)) := by
        simp only [a, nsmul_add, nsmul_sub]
        ring
      rw [heq, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg (by norm_num) n)]
      exact mul_le_mul_of_nonneg_left (hp _ _) (pow_nonneg (by norm_num) n)
    exact sub_eq_zero.mp (tendsto_nhds_unique hlim hzero)
  · intro B
    apply (hN (B + C₂ / 3)).subset
    intro x hx
    have := (abs_le.mp (hclose x)).1
    change q x ≤ B at hx
    change h₀ x ≤ B + C₂ / 3
    linarith

end N25.Alg
