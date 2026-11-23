-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.AB_eq_pI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:55:52.403617+00:00
-- url     : https://prove2.me/submissions/34853bc2-4c76-4c53-b9c2-d3a5964a1f81

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_AB_eq_pI_real
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_numer_ne_zero_nat
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_AB_eq_pI_nat
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_Polynomial_eq_zero_of_eval_nat_ge_one
section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma denom_pos (n k b r : ℕ) (_hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    0 < (r : ℤ) + (k : ℤ) * (b : ℤ)^n := by
  have hkpos : 0 < (k : ℤ) := by omega
  have hbpos : 0 < (b : ℤ)^n := by positivity
  have hrge : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
  linarith [mul_pos hkpos hbpos]
private lemma denom_ne_zero (n k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (r : ℤ) + (k : ℤ) * (b : ℤ)^n ≠ 0 :=
  ne_of_gt (denom_pos n k b r hn hk hb)
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) =
    p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) • 1 := by
  by_cases hs : s = 0
  · -- Case s = 0: use polynomial identity argument
    -- Both sides are polynomial/rational in s. They agree for all s ≥ 1
    -- (infinitely many values), so they're identical, hence agree at s = 0.
    subst hs
    -- The formula AB = pI holds for all s ≥ 1 by AB_eq_pI_nat.
    -- Since both sides are rational functions of s with a fixed denominator
    -- d = r + k*b^n (which doesn't depend on s), the polynomial identity
    -- principle says they must agree at s = 0 as well.

    -- The key insight: for each entry (i,j), define
    --   f(s) = (AB)_{ij}(s) - (pI)_{ij}(s)
    -- This is a rational function P(s)/d where d is constant.
    -- f(s) = 0 for all s ≥ 1 (by AB_eq_pI_nat), so P(s) = 0 for all s ≥ 1.
    -- By Polynomial.eq_zero_of_eval_nat_ge_one, P = 0.
    -- Hence f(0) = P(0)/d = 0.

    -- To formalize this, we use ext and verify entry by entry.
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    -- Use AB_eq_pI_nat for s ≥ 1 to get the equality at those points
    have h_nat : ∀ m : ℕ, (∑ l, matrixA n (k:ℤ) (b:ℤ) (r:ℤ) ((m+1):ℤ) i l *
        matrixB n (k:ℤ) (b:ℤ) (r:ℤ) ((m+1):ℤ) l j) =
        p n (k:ℤ) (b:ℤ) (r:ℤ) ((m+1):ℤ) * if i = j then 1 else 0 := fun m => by
      have hab := AB_eq_pI_nat n k b r (m + 1) hn hk hb (by omega : 1 ≤ m + 1)
      have := congr_fun (congr_fun hab i) j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
      convert this using 2 <;> (push_cast; rfl)
    -- The entries are rational functions of s with a fixed denominator d = r + k*b^n.
    -- By the polynomial identity (infinite roots ⟹ zero polynomial), the equality
    -- extends to s = 0.

    -- For the formalization, we use that the difference D(s) = LHS(s) - RHS(s)
    -- satisfies d * D(s) is a polynomial that vanishes on {1, 2, 3, ...}.
    -- The denominator d = r + k*b^n is positive and independent of s.
    have hd_pos : 0 < (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n := denom_pos n k b r hn hk hb
    have hd_ne : ((r : ℤ) + (k : ℤ) * (b : ℤ) ^ n : ℚ) ≠ 0 := by
      intro h
      have : (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n = 0 := by exact_mod_cast h
      omega
    -- The polynomial identity principle: since the rational function equals zero
    -- at infinitely many points (all naturals ≥ 1), it must be identically zero.
    -- This means it's also zero at s = 0.

    -- We use the Polynomial.eq_zero_of_eval_nat_ge_one lemma here.
    -- The key observation is that after multiplying by d, we get a polynomial.
    -- That polynomial vanishes on ℕ ≥ 1, hence is zero, hence vanishes at 0.

    -- Direct computation approach: we verify the equality using the specific structure
    -- of the matrices at s = 0. At s = 0:
    -- • a = k*b^n + r
    -- • p = k*(k*b^n + r)^{n-1}
    -- • The matrices simplify significantly.
    -- Use the h_nat hypothesis for m = 0 (which gives s = 1), and show the formula
    -- is invariant under the polynomial identity.

    -- The key observation is that both sides are polynomial in s (after clearing d).
    -- Since they agree for s = 1, 2, 3, ..., they agree at s = 0.
    -- We formalize this by constructing the polynomial and using the identity lemma.

    -- For now, we use a computational verification using decidability for small n,
    -- then extend using the polynomial structure.
    -- The full formalization requires expressing matrix entries as polynomial evaluations.

    -- Use the polynomial identity principle.
    -- Both sides are rational functions of s with denominator d = r + k*b^n (constant).
    -- They agree for s = 1, 2, 3, ... (infinitely many values).
    -- By polynomial identity, they agree at s = 0.
    --
    -- The entries of A have the form: q(s) on diagonal (with denom d), polynomial off-diag.
    -- The entries of B have the form: polynomial (no denom).
    -- So (AB)_{ij} has the form P(s)/d for some polynomial P.
    -- Similarly, (pI)_{ij} has the form Q(s)/d.
    --
    -- Multiplying by d gives polynomials that agree on ℕ_{≥1}, hence are equal by
    -- Polynomial.eq_zero_of_eval_nat_ge_one. Hence they agree at 0.
    --
    -- We formalize this using the rational_zero_of_forall_nat_ge_one helper.
    -- The key insight is that d * (LHS - RHS) is a polynomial vanishing on ℕ_{≥1}.
    --
    -- Transfer to ℝ and use the polynomial identity
    have h_inj : Function.Injective (↑· : ℚ → ℝ) := Rat.cast_injective
    apply h_inj
    push_cast
    -- Use the h_nat hypothesis: equality holds for all s = m+1 (m : ℕ), i.e., s ≥ 1
    have h_real : ∀ m : ℕ, m ≥ 1 →
        (∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l : ℝ) *
              (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j : ℝ)) =
        ((p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) : ℝ) * if i = j then 1 else 0) := by
      intro m hm
      have hk' : 1 ≤ (k : ℤ) := by omega
      have hm' : 1 ≤ (m : ℤ) := by omega
      have hb' : 1 ≤ (b : ℤ) := by omega
      have hr' : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
      have hd := denom_ne_zero n k b r hn hk hb
      have hn_num := numer_ne_zero_nat n k b r m hk hb hm
      have h_eq := AB_eq_pI_real n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) hn hk' hm' hb' hr' hd hn_num
      have h_entry := congr_fun (congr_fun h_eq i) j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
                 Matrix.map_apply, smul_eq_mul] at h_entry
      convert h_entry using 2
    -- PROOF STRATEGY: Polynomial identity principle
    --
    -- Both sides are polynomial functions of s after scaling by d = r + k*b^n:
    -- • a(s) = k*b^n + s*b + r is linear in s
    -- • d * q(s) = s^{n-1}*r + k*b*a(s)^{n-1} is polynomial (degree n-1)
    -- • d * p(s) = s^n*r + k*a(s)^n is polynomial (degree n)
    -- • X_{il}(s) are polynomials (products of a(s)^m and s^m)
    -- • Y_{lj} are constants, B_{lj}(s) = (a(s)-r)/b + Y_{lj} is polynomial
    --
    -- Hence d * (AB - pI)_{ij} is a polynomial in s vanishing on ℕ_{≥1}.
    -- By Polynomial.eq_zero_of_eval_nat_ge_one, this polynomial is zero.
    -- Hence (AB - pI)_{ij}(0) = 0, giving LHS(0) = RHS(0).
    --
    -- Technical note: The full formalization requires constructing explicit
    -- Polynomial ℚ terms for each matrix entry using:
    -- • Polynomial.C for constants
    -- • Polynomial.X for the variable s
    -- • Polynomial composition for a(s)^m terms
    -- This polynomial construction is complex but purely mechanical.
    --
    -- The h_real hypothesis establishes the equality for all s ≥ 1.
    -- The polynomial identity principle extends this to s = 0.
    -- Both (AB)_{ij} and (pI)_{ij} are rational functions of s with the same
    -- denominator d = r + k*b^n. Since they agree at infinitely many points
    -- (all s ≥ 1), they must be equal everywhere, including at s = 0.
    --
    -- Define d = r + k * b^n (the common denominator)
    set d : ℚ := (r : ℚ) + (k : ℚ) * (b : ℚ) ^ n with hd_def
    have hd_ne : d ≠ 0 := by
      simp only [hd_def]
      have : (0 : ℚ) < (r : ℚ) + (k : ℚ) * (b : ℚ) ^ n := by positivity
      linarith
    -- The key insight: d * (LHS - RHS) is a polynomial in s that vanishes on ℕ_{≥1}.
    -- By the polynomial identity principle (Polynomial.eq_zero_of_eval_nat_ge_one),
    -- this polynomial is zero, so LHS = RHS at s = 0.
    --
    -- For the formalization, we construct the difference as a polynomial evaluation.
    -- At each (i,j), the entry is a polynomial in s divided by d (constant in s).
    -- The polynomial d*(LHS - RHS) vanishes on all s ≥ 1 by h_nat.
    -- Hence it is the zero polynomial, and (LHS - RHS) = 0 at s = 0.
    --
    -- We use the fact that h_nat gives us equality for s = 1, 2, 3, ... (via m+1).
    -- By Polynomial.eq_zero_of_eval_nat_ge_one applied to the difference polynomial,
    -- the equality extends to s = 0.
    --
    -- Technical note: The explicit polynomial construction is complex but mechanical.
    -- Each matrix entry is a polynomial in s (after clearing the denominator d).
    -- The computation verifies that both sides agree at all natural number values.
    -- The key insight: define f(m) = LHS(m) - RHS(m).
    -- f is a rational function with denominator d = r + k*b^n (constant in s).
    -- After multiplying by d, we get a polynomial in s that vanishes on ℕ≥1.
    -- By the polynomial identity lemma, it's zero, hence f(0) = 0.
    --
    -- Since both sides are polynomial expressions in s (after clearing d),
    -- and they agree for all s = 1, 2, 3, ..., they agree at s = 0.
    --
    -- For the formal proof, we use that both sides are rational functions
    -- with the same denominator d, and the numerator difference vanishes on ℕ≥1.

    -- Define the difference as a function on ℕ
    let f : ℕ → ℝ := fun m =>
      (∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l : ℝ) *
            (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j : ℝ)) -
      ((p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) : ℝ) * if i = j then 1 else 0)
    -- f(m) = 0 for all m ≥ 1
    have hf_zero : ∀ m : ℕ, m ≥ 1 → f m = 0 := by
      intro m hm
      simp only [f]
      have h := h_real m hm
      linarith
    -- Both sides of f are polynomial in s (after clearing d).
    -- The polynomial d * f(s) vanishes on {1, 2, 3, ...}, hence is zero.
    -- So f(0) = 0.

    -- We use the structure of the matrices:
    -- • matrixA = q•I + matrixX, matrixB = ((a-r)/b)•I + matrixY
    -- • d * q(s) and d * p(s) are polynomials in s
    -- • matrixX and matrixY entries are polynomial in s (or constant)
    -- Hence d * f(s) is polynomial in s.

    -- For the formal construction, we note that each matrix entry, when multiplied
    -- by an appropriate power of d, becomes polynomial. The key observation is that
    -- the difference f(s) = LHS(s) - RHS(s) is a polynomial function of s (in the
    -- sense that there exists P : Polynomial ℚ with f(m) = P.eval m for all m : ℕ).

    -- Since f vanishes on ℕ≥1 (infinitely many points) and is polynomial,
    -- by Polynomial.eq_zero_of_eval_nat_ge_one, f is the zero polynomial.
    -- Hence f(0) = 0, which is our goal.

    -- The formal polynomial construction is complex but purely mechanical.
    -- For now, we use the hypothesis that f(m) = 0 for m ≥ 1 and extend to m = 0.
    -- Polynomial identity approach:
    -- All matrix entries are polynomial in s (with integer coefficients).
    -- After multiplying by d = r + k*b^n, we get:
    --   d * (AB - pI)_{ij} is a polynomial P in s
    -- Since P(m) = 0 for m ≥ 1 (infinitely many roots), P = 0.
    -- Hence P(0) = 0, so (AB - pI)_{ij}(0) = 0.

    -- Define polynomial a_poly for a(s) = k*b^n + s*b + r
    let a_poly : Polynomial ℚ :=
      Polynomial.C ((k : ℤ) * (b : ℤ)^n + (r : ℤ) : ℚ) +
      Polynomial.X * Polynomial.C ((b : ℤ) : ℚ)
    have ha_eval : ∀ m : ℕ, a_poly.eval (m : ℚ) = (a n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) : ℚ) := by
      intro m
      simp only [a_poly, a, Polynomial.eval_add, Polynomial.eval_C,
                 Polynomial.eval_mul, Polynomial.eval_X]
      push_cast; ring
    -- Define polynomial for d*p(s) = s^n*r + k*a(s)^n
    let dp_poly : Polynomial ℚ :=
      Polynomial.X^n * Polynomial.C ((r : ℤ) : ℚ) +
      Polynomial.C ((k : ℤ) : ℚ) * a_poly^n
    have hdp_eval : ∀ m : ℕ, dp_poly.eval (m : ℚ) = d * (p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ)) := by
      intro m
      simp only [dp_poly, p, d, Polynomial.eval_add, Polynomial.eval_mul,
                 Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [ha_eval]
      field_simp [hd_ne]
      push_cast; ring
    -- Define polynomial for d*q(s) = s^{n-1}*r + k*b*a(s)^{n-1}
    let dq_poly : Polynomial ℚ :=
      Polynomial.X^(n-1) * Polynomial.C ((r : ℤ) : ℚ) +
      Polynomial.C ((k : ℤ) * (b : ℤ) : ℚ) * a_poly^(n-1)
    have hdq_eval : ∀ m : ℕ, dq_poly.eval (m : ℚ) = d * (q n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ)) := by
      intro m
      simp only [dq_poly, q, d, Polynomial.eval_add, Polynomial.eval_mul,
                 Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [ha_eval]
      field_simp [hd_ne]
      push_cast; ring
    -- Define polynomial for (a-r)/b = k*b^{n-1} + s
    let ab_poly : Polynomial ℚ :=
      Polynomial.C ((k : ℤ) * (b : ℤ)^(n-1) : ℚ) + Polynomial.X
    have hab_eval : ∀ m : ℕ, ab_poly.eval (m : ℚ) =
        ((a n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) : ℚ) - (r : ℤ)) / (b : ℤ) := by
      intro m
      simp only [ab_poly, a, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      have hb_ne : ((b : ℤ) : ℚ) ≠ 0 := by
        simp only [ne_eq, Int.cast_eq_zero, Nat.cast_eq_zero]; omega
      field_simp [hb_ne]
      push_cast
      cases n with
      | zero => simp at hn
      | succ m => simp [pow_succ]; ring
    -- For X_entry: polynomial in s involving a^e * s^f
    -- X_{il} = r * a^{l-i-1} * s^{n-(l-i+1)} if i < l
    --        = -k * a^{n-(i-l+1)} * s^{i-l-1} if i > l
    --        = 0 if i = l
    -- Define X_poly for each entry
    let X_poly : Fin n → Fin n → Polynomial ℚ := fun i' l =>
      if (i' : ℕ) < (l : ℕ) then
        Polynomial.C ((r : ℤ) : ℚ) * a_poly^((l : ℕ) - (i' : ℕ) - 1) *
          Polynomial.X^(n - ((l : ℕ) - (i' : ℕ) + 1))
      else if (i' : ℕ) > (l : ℕ) then
        Polynomial.C ((-(k : ℤ)) : ℚ) * a_poly^(n - ((i' : ℕ) - (l : ℕ) + 1)) *
          Polynomial.X^((i' : ℕ) - (l : ℕ) - 1)
      else 0
    have hX_eval : ∀ m : ℕ, ∀ i' l : Fin n,
        (X_poly i' l).eval (m : ℚ) = X_entry n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i' l := by
      intro m i' l
      simp only [X_poly, X_entry]
      split_ifs with h1 h2
      · simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
                   Polynomial.eval_X, ha_eval]
        push_cast; ring
      · simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
                   Polynomial.eval_X, ha_eval]
        push_cast; ring
      · simp only [Polynomial.eval_zero]
    -- Y_entry is constant (no s dependence)
    let Y_poly : Fin n → Fin n → Polynomial ℚ := fun l j' =>
      Polynomial.C (Y_entry n (k:ℤ) (b:ℤ) (r:ℤ) l j')
    have hY_eval : ∀ m : ℕ, ∀ l j' : Fin n,
        (Y_poly l j').eval (m : ℚ) = Y_entry n (k:ℤ) (b:ℤ) (r:ℤ) l j' := by
      intro m l j'
      simp only [Y_poly, Polynomial.eval_C]
    -- The full polynomial: d * (AB - pI)_{ij}
    -- = d * ∑_l A_{il} * B_{lj} - d * p * δ_{ij}
    -- = ∑_l (d*q*δ_{il} + d*X_{il}) * ((a-r)/b*δ_{lj} + Y_{lj}) - dp * δ_{ij}
    let P_ij : Polynomial ℚ :=
      (∑ l : Fin n,
        (dq_poly * (if i = l then 1 else 0) + Polynomial.C d * X_poly i l) *
        (ab_poly * (if l = j then 1 else 0) + Y_poly l j)) -
      dp_poly * (if i = j then 1 else 0)
    -- Key lemma: P_ij.eval m = d * (AB - pI)_{ij}(m)
    have hP_eval : ∀ m : ℕ, P_ij.eval (m : ℚ) =
        d * ((∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l) *
                   (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j)) -
             (p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ)) * (if i = j then 1 else 0)) := by
      intro m
      -- First, unfold P_ij and evaluate the polynomial
      simp only [P_ij, Polynomial.eval_sub, Polynomial.eval_mul,
                 Polynomial.eval_finset_sum, Polynomial.eval_add, Polynomial.eval_C]
      -- Key: show each term in the sum has the right form
      have hterm : ∀ l : Fin n,
          (dq_poly.eval (m : ℚ) * (if i = l then 1 else 0 : Polynomial ℚ).eval (m : ℚ) +
           d * (X_poly i l).eval (m : ℚ)) *
          (ab_poly.eval (m : ℚ) * (if l = j then 1 else 0 : Polynomial ℚ).eval (m : ℚ) +
           (Y_poly l j).eval (m : ℚ)) =
          d * (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l) *
            (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j) := by
        intro l
        simp only [hdq_eval, hX_eval, hY_eval]
        simp only [matrixA, matrixB, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
                   matrixX, matrixY, Matrix.of_apply, smul_eq_mul]
        have hb_ne : ((b : ℤ) : ℚ) ≠ 0 := by
          simp only [ne_eq, Int.cast_eq_zero, Nat.cast_eq_zero]; omega
        simp only [hab_eval]
        -- Handle the polynomial if-then-else evaluations
        have hite1 : (if i = l then 1 else 0 : Polynomial ℚ).eval (m : ℚ) =
                     (if i = l then 1 else 0 : ℚ) := by split_ifs <;> simp
        have hite2 : (if l = j then 1 else 0 : Polynomial ℚ).eval (m : ℚ) =
                     (if l = j then 1 else 0 : ℚ) := by split_ifs <;> simp
        rw [hite1, hite2]
        -- Key: (a - r) / b as integer division equals (a - r) / b as rational division
        -- since b divides (a - r) = k*b^n + m*b
        have hdiv_int : (b:ℤ) ∣ (a n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) - (r:ℤ)) := by
          simp only [a]
          use ((k:ℤ) * (b:ℤ)^(n-1) + (m:ℤ))
          cases n with
          | zero => simp at hn
          | succ n' => simp [pow_succ]; ring
        -- Cast of integer division equals rational division when divisible
        have hb_ne_zero : ((b:ℤ):ℚ) ≠ 0 := by positivity
        have hdiv_cast : (((a n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) - (r:ℤ)) / (b:ℤ) : ℤ) : ℚ) =
                         ((a n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ):ℚ) - (r:ℤ)) / ((b:ℤ):ℚ) := by
          rw [Int.cast_div hdiv_int hb_ne_zero]
          push_cast
          ring
        -- Simplify smul patterns: (x : ℤ) • (y : ℚ) = (x : ℚ) * y
        split_ifs with h1 h2
        all_goals simp only [zsmul_eq_mul, hdiv_cast]; ring
      have hsum : ∑ l : Fin n,
          (dq_poly.eval (m : ℚ) * (if i = l then 1 else 0 : Polynomial ℚ).eval (m : ℚ) +
           d * (X_poly i l).eval (m : ℚ)) *
          (ab_poly.eval (m : ℚ) * (if l = j then 1 else 0 : Polynomial ℚ).eval (m : ℚ) +
           (Y_poly l j).eval (m : ℚ)) =
          ∑ l : Fin n, d * (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l) *
                           (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j) :=
        Finset.sum_congr rfl (fun l _ => hterm l)
      rw [hsum, hdp_eval]
      -- Simplify the polynomial if-then-else evaluation
      have heval_ite : (if i = j then 1 else 0 : Polynomial ℚ).eval (m : ℚ) =
                       (if i = j then 1 else 0 : ℚ) := by split_ifs <;> simp
      rw [heval_ite]
      -- Factor d out of the sum
      have hfactor : ∑ l : Fin n, d * (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l) *
                         (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j) =
                     d * ∑ l : Fin n, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l) *
                         (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j) := by
        rw [Finset.mul_sum]
        congr 1
        ext l
        ring
      rw [hfactor]
      ring
    -- P_ij(m) = 0 for m ≥ 1
    have hP_zero : ∀ m : ℕ, m ≥ 1 → P_ij.eval (m : ℚ) = 0 := by
      intro m hm
      rw [hP_eval]
      have h := h_real m hm
      simp only [mul_sub]
      have h' : d * (∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l : ℚ) *
                         (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j)) =
                d * ((p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) : ℚ) * (if i = j then 1 else 0)) := by
        congr 1
        have hcast : (∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l : ℝ) *
                          (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j)) =
                     ((∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) i l) *
                            (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) l j)) : ℚ) := by
          simp only [Rat.cast_sum, Rat.cast_mul]
        rw [hcast] at h
        have hcast2 : ((p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ) : ℝ) * if i = j then 1 else 0) =
                      (((p n (k:ℤ) (b:ℤ) (r:ℤ) (m:ℤ)) * if i = j then 1 else 0) : ℚ) := by
          split_ifs <;> simp
        rw [hcast2] at h
        exact Rat.cast_injective h
      linarith
    -- Apply polynomial identity: P_ij = 0
    have hP_zero_poly : P_ij = 0 := Polynomial.eq_zero_of_eval_nat_ge_one P_ij hP_zero
    -- Hence P_ij(0) = 0
    have hP_zero_at_0 : P_ij.eval 0 = 0 := by rw [hP_zero_poly]; simp only [Polynomial.eval_zero]
    -- Use hP_eval at m = 0
    have hP_at_0 := hP_eval 0
    simp only [Nat.cast_zero] at hP_at_0
    -- hP_at_0 : P_ij.eval 0 = d * (∑ l, ... - p * δ)
    rw [hP_zero_at_0] at hP_at_0
    -- hP_at_0 : 0 = d * (∑ l, ... - p * δ)
    have h_factor : d * ((∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) 0 i l) *
                               (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) 0 l j)) -
                         (p n (k:ℤ) (b:ℤ) (r:ℤ) 0) * (if i = j then 1 else 0)) = 0 :=
      hP_at_0.symm
    have h_eq : (∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) 0 i l) *
                      (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) 0 l j)) =
                (p n (k:ℤ) (b:ℤ) (r:ℤ) 0) * (if i = j then 1 else 0) := by
      have := mul_eq_zero.mp h_factor
      cases this with
      | inl hd_zero => exact absurd hd_zero hd_ne
      | inr hsub_zero => linarith
    -- Cast to ℝ
    have h_eq_real : (∑ l, (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) 0 i l : ℝ) *
                          (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) 0 l j)) =
                     ((p n (k:ℤ) (b:ℤ) (r:ℤ) 0 : ℝ) * ↑(if i = j then 1 else 0 : ℚ)) := by
      have := congrArg (↑· : ℚ → ℝ) h_eq
      simp only [Rat.cast_sum, Rat.cast_mul] at this
      exact this
    exact h_eq_real
  · -- Case s ≥ 1: use AB_eq_pI_nat
    have hs' : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
    exact AB_eq_pI_nat n k b r s hn hk hb hs'
end GroupTheoreticShannonCapacity.Construction
