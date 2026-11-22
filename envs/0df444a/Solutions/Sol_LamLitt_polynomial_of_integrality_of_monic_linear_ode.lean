-- Prove2me | solution 1 for LamLitt.polynomial_of_integrality_of_monic_linear_ode
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:30:40.102188+00:00
-- url     : https://prove2.me/submissions/8b030975-11c3-4e37-abdd-254e18addae6

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_polynomial_of_integrality_of_entire
import Mathlib

/-!
# Linear ODEs with polynomial coefficients: bounded denominators force a polynomial

Let `f = ∑ aₖ zᵏ ∈ ℚ⟦z⟧` satisfy `f⁽ⁿ⁾ = r(z) + ∑_{i<n} cᵢ(z) f⁽ⁱ⁾` with `r, cᵢ ∈ ℚ[z]`.
If all `aₖ` lie in `ℤ[1/N]`, then `f` is a polynomial.

This is a reduction to `LamLitt.polynomial_of_integrality_of_entire`. We supply

* the ODE witness `g = r(z) + ∑ cᵢ(z) yᵢ` (a polynomial, so the denominator is `1`), and
* the growth bound `sup_k |aₖ| Rᵏ < ∞` for every `R`, which follows from the coefficient
  recurrence
  `(k+1)⋯(k+n) a_{k+n} = r_k + ∑_i ∑_{j+l=k} c_{i,j} (l+1)⋯(l+i) a_{l+i}`:
  for `k` larger than the degrees, the left factor is `≥ (k+1)ⁿ` while each factor on the
  right is `≤ (n(k+1))^(n-1)`, so the weighted sequence `|a_l| ρ^l` (`ρ = R + 1`) cannot exceed
  the sum `C` of its first `K₀ + n` terms, where `K₀ > d` and `K₀ ≥ A · n^(n-1) · ρ^(d+n)`
  (strong induction on the index).
-/

set_option autoImplicit false

open PowerSeries

namespace LamLittAuxL

/-- `[X^l] f^{(i)} = (l+1)(l+2)⋯(l+i) · [X^{l+i}] f`. -/
lemma coeff_iterate_derivative (i : ℕ) : ∀ (f : ℚ⟦X⟧) (l : ℕ),
    coeff l ((d⁄dX ℚ)^[i] f) = ((l + 1).ascFactorial i : ℚ) * coeff (l + i) f := by
  induction i with
  | zero => intro f l; simp
  | succ i ih =>
    intro f l
    rw [Function.iterate_succ_apply, ih, coeff_derivative, Nat.ascFactorial_succ,
      show l + (i + 1) = l + i + 1 by ring]
    push_cast
    ring

/-- Comparing the coefficients of `X^k` in the linear ODE. -/
lemma coeff_recurrence {n : ℕ} (f : ℚ⟦X⟧) (c : Fin n → Polynomial ℚ) (r : Polynomial ℚ)
    (hODE : (d⁄dX ℚ)^[n] f =
      (r : ℚ⟦X⟧) + ∑ i : Fin n, (c i : ℚ⟦X⟧) * (d⁄dX ℚ)^[i.val] f) (k : ℕ) :
    ((k + 1).ascFactorial n : ℚ) * coeff (k + n) f =
      r.coeff k + ∑ i : Fin n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        (c i).coeff p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * coeff (p.2 + i.val) f) := by
  have h := congrArg (coeff k) hODE
  rw [coeff_iterate_derivative, map_add, Polynomial.coeff_coe, map_sum] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Polynomial.coeff_coe, coeff_iterate_derivative]

/-- Bound for one term of the recurrence. -/
lemma term_bound (a : ℕ → ℚ) (ρ C : ℚ) (hρ : 1 ≤ ρ) (hC : 0 ≤ C) (m d k l i j : ℕ)
    (hi : i ≤ m) (hj : j ≤ d) (hjl : j + l = k) (ha : |a (l + i)| * ρ ^ (l + i) ≤ C) :
    ((l + 1).ascFactorial i : ℚ) * (|a (l + i)| * ρ ^ (k + (m + 1)))
      ≤ (((m + 1) * (k + 1) : ℕ) : ℚ) ^ m * C * ρ ^ (d + m + 1) := by
  have hρ0 : 0 ≤ ρ := by linarith
  have h1 : ((l + 1).ascFactorial i : ℚ) ≤ (((m + 1) * (k + 1) : ℕ) : ℚ) ^ m := by
    have hlk : l + i ≤ (m + 1) * (k + 1) := by nlinarith [Nat.zero_le (m * k)]
    have : (l + 1).ascFactorial i ≤ ((m + 1) * (k + 1)) ^ m := calc
      (l + 1).ascFactorial i ≤ (l + i) ^ i := Nat.ascFactorial_le_pow_add l i
      _ ≤ ((m + 1) * (k + 1)) ^ i := Nat.pow_le_pow_left hlk i
      _ ≤ ((m + 1) * (k + 1)) ^ m := Nat.pow_le_pow_right (by positivity) hi
    exact_mod_cast this
  have h2 : |a (l + i)| * ρ ^ (k + (m + 1)) ≤ C * ρ ^ (d + m + 1) := by
    obtain ⟨e, he, he'⟩ : ∃ e, k + (m + 1) = (l + i) + e ∧ e ≤ d + m + 1 :=
      ⟨j + (m + 1 - i), by omega, by omega⟩
    rw [he, pow_add, ← mul_assoc]
    exact mul_le_mul ha (pow_le_pow_right₀ hρ he') (by positivity) hC
  calc ((l + 1).ascFactorial i : ℚ) * (|a (l + i)| * ρ ^ (k + (m + 1)))
      ≤ (((m + 1) * (k + 1) : ℕ) : ℚ) ^ m * (C * ρ ^ (d + m + 1)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- The inductive step: once `k + 1` exceeds the threshold, the bound `C` propagates. -/
lemma step (m d : ℕ) (a : ℕ → ℚ) (cc : Fin (m + 1) → ℕ → ℚ)
    (hcc : ∀ i j, d < j → cc i j = 0) (k : ℕ) (hk : d < k)
    (hrec : ((k + 1).ascFactorial (m + 1) : ℚ) * a (k + (m + 1)) =
      ∑ i : Fin (m + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        cc i p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * a (p.2 + i.val)))
    (ρ C : ℚ) (hρ : 1 ≤ ρ) (hC0 : 0 ≤ C)
    (hbig : (∑ i : Fin (m + 1), ∑ j ∈ Finset.range (d + 1), |cc i j|)
      * ((m + 1 : ℕ) : ℚ) ^ m * ρ ^ (d + m + 1) ≤ (k : ℚ) + 1)
    (hC : ∀ l, l < k + (m + 1) → |a l| * ρ ^ l ≤ C) :
    |a (k + (m + 1))| * ρ ^ (k + (m + 1)) ≤ C := by
  have hρ0 : 0 ≤ ρ := by linarith
  set B : ℚ := (((m + 1) * (k + 1) : ℕ) : ℚ) ^ m * C * ρ ^ (d + m + 1) with hBdef
  have hB : 0 ≤ B := by positivity
  have hsum : ∀ i : Fin (m + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      |cc i p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * a (p.2 + i.val))| * ρ ^ (k + (m + 1))
        ≤ (∑ j ∈ Finset.range (d + 1), |cc i j|) * B := by
    intro i
    calc ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          |cc i p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * a (p.2 + i.val))|
            * ρ ^ (k + (m + 1))
        ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, |cc i p.1| * B := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          by_cases hj : p.1 ≤ d
          · rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc, mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact term_bound a ρ C hρ hC0 m d k p.2 i p.1 (Nat.lt_succ_iff.mp i.2) hj hp
              (hC _ (by omega))
          · rw [hcc i p.1 (by omega)]; simp
      _ = (∑ j ∈ Finset.range (k + 1), |cc i j|) * B := by
          rw [Finset.sum_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => |cc i p.1| * B)]
      _ = (∑ j ∈ Finset.range (d + 1), |cc i j|) * B := by
          congr 1
          symm
          refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
          rw [Finset.mem_range, not_lt] at hj
          rw [hcc i j (by omega), abs_zero]
  have hmain : ((k : ℚ) + 1) ^ (m + 1) * (|a (k + (m + 1))| * ρ ^ (k + (m + 1)))
      ≤ (∑ i : Fin (m + 1), ∑ j ∈ Finset.range (d + 1), |cc i j|) * B := by
    have hasc : ((k : ℚ) + 1) ^ (m + 1) ≤ ((k + 1).ascFactorial (m + 1) : ℚ) := by
      exact_mod_cast Nat.pow_succ_le_ascFactorial (k + 1) (m + 1)
    calc ((k : ℚ) + 1) ^ (m + 1) * (|a (k + (m + 1))| * ρ ^ (k + (m + 1)))
        ≤ ((k + 1).ascFactorial (m + 1) : ℚ) * (|a (k + (m + 1))| * ρ ^ (k + (m + 1))) :=
          mul_le_mul_of_nonneg_right hasc (by positivity)
      _ = |((k + 1).ascFactorial (m + 1) : ℚ) * a (k + (m + 1))| * ρ ^ (k + (m + 1)) := by
          rw [abs_mul, Nat.abs_cast, mul_assoc]
      _ ≤ (∑ i : Fin (m + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
            |cc i p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * a (p.2 + i.val))|)
              * ρ ^ (k + (m + 1)) := by
          rw [hrec]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i : Fin (m + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
            |cc i p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * a (p.2 + i.val))|
              * ρ ^ (k + (m + 1)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
      _ ≤ ∑ i : Fin (m + 1), (∑ j ∈ Finset.range (d + 1), |cc i j|) * B :=
          Finset.sum_le_sum fun i _ => hsum i
      _ = (∑ i : Fin (m + 1), ∑ j ∈ Finset.range (d + 1), |cc i j|) * B := by
          rw [Finset.sum_mul]
  have hk1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hfin : ((k : ℚ) + 1) ^ (m + 1) * (|a (k + (m + 1))| * ρ ^ (k + (m + 1)))
      ≤ ((k : ℚ) + 1) ^ (m + 1) * C := by
    calc ((k : ℚ) + 1) ^ (m + 1) * (|a (k + (m + 1))| * ρ ^ (k + (m + 1)))
        ≤ (∑ i : Fin (m + 1), ∑ j ∈ Finset.range (d + 1), |cc i j|) * B := hmain
      _ = ((∑ i : Fin (m + 1), ∑ j ∈ Finset.range (d + 1), |cc i j|)
            * ((m + 1 : ℕ) : ℚ) ^ m * ρ ^ (d + m + 1)) * (C * ((k : ℚ) + 1) ^ m) := by
          rw [hBdef]; push_cast; rw [mul_pow]; ring
      _ ≤ ((k : ℚ) + 1) * (C * ((k : ℚ) + 1) ^ m) :=
          mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = ((k : ℚ) + 1) ^ (m + 1) * C := by ring
  exact le_of_mul_le_mul_left hfin (by positivity)

/-- Growth bound for sequences satisfying the recurrence: `|a k| R^k` is bounded for every `R`. -/
lemma growth (m d : ℕ) (a : ℕ → ℚ) (cc : Fin (m + 1) → ℕ → ℚ)
    (hcc : ∀ i j, d < j → cc i j = 0)
    (hrec : ∀ k, d < k → ((k + 1).ascFactorial (m + 1) : ℚ) * a (k + (m + 1)) =
      ∑ i : Fin (m + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        cc i p.1 * (((p.2 + 1).ascFactorial i.val : ℚ) * a (p.2 + i.val)))
    (R : ℕ) : ∃ C : ℚ, ∀ k : ℕ, |a k| * (R : ℚ) ^ k ≤ C := by
  set ρ : ℚ := (R : ℚ) + 1 with hρdef
  have hρ : 1 ≤ ρ := by rw [hρdef]; linarith [(Nat.cast_nonneg R : (0 : ℚ) ≤ (R : ℚ))]
  have hρ0 : 0 ≤ ρ := by linarith
  set M : ℚ := (∑ i : Fin (m + 1), ∑ j ∈ Finset.range (d + 1), |cc i j|)
      * ((m + 1 : ℕ) : ℚ) ^ m * ρ ^ (d + m + 1) with hMdef
  set K₀ : ℕ := d + 1 + ⌈M⌉₊ with hK₀
  have hMK : M ≤ (K₀ : ℚ) := by
    refine (Nat.le_ceil M).trans ?_
    exact_mod_cast (by omega : ⌈M⌉₊ ≤ K₀)
  set C : ℚ := ∑ l ∈ Finset.range (K₀ + (m + 1)), |a l| * ρ ^ l with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => by positivity
  have key : ∀ l, |a l| * ρ ^ l ≤ C := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      by_cases hl : l < K₀ + (m + 1)
      · exact Finset.single_le_sum (f := fun l => |a l| * ρ ^ l) (fun _ _ => by positivity)
          (Finset.mem_range.2 hl)
      · obtain ⟨k, rfl⟩ : ∃ k, l = k + (m + 1) := ⟨l - (m + 1), by omega⟩
        have hKk : (K₀ : ℚ) ≤ (k : ℚ) := by exact_mod_cast (by omega : K₀ ≤ k)
        exact step m d a cc hcc k (by omega) (hrec k (by omega)) ρ C hρ hC0
          (by linarith) (fun l hl => ih l hl)
  refine ⟨C, fun k => le_trans ?_ (key k)⟩
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg R) ?_ k) (abs_nonneg _)
  rw [hρdef]; linarith

/-- A polynomial viewed as a power series is its evaluation at `X`. -/
lemma aeval_X_eq_coe (s : Polynomial ℚ) :
    Polynomial.aeval (PowerSeries.X : ℚ⟦X⟧) s = (s : ℚ⟦X⟧) := by
  rw [Polynomial.aeval_def, ← Polynomial.eval₂_C_X_eq_coe]
  rfl

/-- Evaluating a polynomial in the variable `z = X 0` at a point whose `0`-th coordinate is `X`. -/
lemma aeval_aeval_X0 {n : ℕ} (pt : Fin (n + 1) → ℚ⟦X⟧) (h0 : pt 0 = PowerSeries.X)
    (s : Polynomial ℚ) :
    MvPolynomial.aeval pt
        (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) ℚ) s) = (s : ℚ⟦X⟧) := by
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, h0, aeval_X_eq_coe]

/-- The right-hand side `r(z) + ∑ cᵢ(z) yᵢ` of the linear ODE as a multivariate polynomial. -/
noncomputable def rhs {n : ℕ} (c : Fin n → Polynomial ℚ) (r : Polynomial ℚ) :
    MvPolynomial (Fin (n + 1)) ℚ :=
  Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) ℚ) r +
    ∑ i : Fin n, Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) ℚ) (c i)
      * MvPolynomial.X i.succ

/-- The linear ODE is an algebraic ODE in the sense of the platform definition. -/
lemma isSolution {n : ℕ} (f : ℚ⟦X⟧) (c : Fin n → Polynomial ℚ) (r : Polynomial ℚ)
    (hODE : (d⁄dX ℚ)^[n] f =
      (r : ℚ⟦X⟧) + ∑ i : Fin n, (c i : ℚ⟦X⟧) * (d⁄dX ℚ)^[i.val] f) :
    LamLitt.IsSolutionOfAlgebraicODE n f
      (algebraMap _ _ (rhs c r) / algebraMap _ _ (1 : MvPolynomial (Fin (n + 1)) ℚ)) := by
  refine ⟨rhs c r, 1, rfl, ?_, ?_⟩
  · rw [map_one]; exact one_ne_zero
  · rw [map_one, mul_one, hODE, rhs, map_add, map_sum, aeval_aeval_X0 _ rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_aeval_X0 _ rfl, MvPolynomial.aeval_X]
    rfl

end LamLittAuxL

open LamLitt PowerSeries in
theorem solution {n : ℕ} (f : PowerSeries ℚ)
    (c : Fin n → Polynomial ℚ) (r : Polynomial ℚ)
    (hODE : (PowerSeries.derivative ℚ)^[n] f =
      (r : PowerSeries ℚ) +
        ∑ i : Fin n, (c i : PowerSeries ℚ) * (PowerSeries.derivative ℚ)^[i.val] f)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    ∃ P : Polynomial ℚ, f = (P : PowerSeries ℚ) := by
  refine polynomial_of_integrality_of_entire f _ (LamLittAuxL.isSolution f c r hODE) N hN ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `n = 0`: the equation reads `f = r`
    subst h0
    have hf : f = (r : PowerSeries ℚ) := by simpa using hODE
    intro R
    refine ⟨∑ l ∈ Finset.range (r.natDegree + 1), |r.coeff l| * (R : ℚ) ^ l, fun k => ?_⟩
    rw [hf, Polynomial.coeff_coe]
    by_cases hk : k < r.natDegree + 1
    · exact Finset.single_le_sum (f := fun l => |r.coeff l| * (R : ℚ) ^ l)
        (fun _ _ => by positivity) (Finset.mem_range.2 hk)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero, zero_mul]
      exact Finset.sum_nonneg fun _ _ => by positivity
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set d : ℕ := r.natDegree + ∑ i : Fin (m + 1), (c i).natDegree with hd
    have hdc : ∀ i : Fin (m + 1), (c i).natDegree ≤ d := fun i =>
      le_trans (Finset.single_le_sum (f := fun i : Fin (m + 1) => (c i).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
    refine LamLittAuxL.growth m d (fun k => PowerSeries.coeff k f) (fun i j => (c i).coeff j)
      (fun i j hj => Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdc i) hj))
      (fun k hk => ?_)
    have h := LamLittAuxL.coeff_recurrence f c r hODE k
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_add] at h
    exact h
