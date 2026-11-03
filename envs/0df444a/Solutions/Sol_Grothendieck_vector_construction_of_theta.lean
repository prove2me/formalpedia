-- Prove2me | solution 1 for Grothendieck.vector_construction_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:32:26.624712+00:00
-- url     : https://prove2.me/submissions/da80af28-5052-4d01-8adc-a8ccb6ba5df4

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Beta
import Definitions.Def_Grothendieck_Theta

/-!
# Elementary bounds for the coefficients of `E_r`

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite
programs with rank constraint*, Theory of Computing 10(4), 2014.

For `r ≥ 1` every coefficient `ErCoeff r k` is positive, and the coefficients are
summable, with the explicit bound

`ErCoeff r k ≤ C_r (k+1)^{-3/2}`.

The proof only uses elementary product manipulations: writing `A_k = (1/2)_k` and
`B_k = (r/2+1)_k` one has `B_k ≥ (3/2)_k = (2k+1) A_k` and `A_k/k! ≤ 1/√(k+1)`.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

/-! ### Positivity -/

theorem risingFact_succ (a : ℝ) (k : ℕ) :
    risingFact a (k + 1) = risingFact a k * (a + (k : ℝ)) := by
  simp [risingFact, Finset.prod_range_succ]

theorem risingFact_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < risingFact a k := by
  unfold risingFact
  exact Finset.prod_pos fun i _ => by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith

theorem risingFact_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ risingFact a k := by
  unfold risingFact
  exact Finset.prod_nonneg fun i _ => by
    have h : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith

theorem Cr_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h2 : (0 : ℝ) < ((r : ℝ) + 1) / 2 := by linarith
  have h3 : (0 : ℝ) < (r : ℝ) / 2 := by linarith
  have hq : 0 < Real.Gamma (((r : ℝ) + 1) / 2) / Real.Gamma ((r : ℝ) / 2) :=
    div_pos (Real.Gamma_pos_of_pos h2) (Real.Gamma_pos_of_pos h3)
  unfold Cr
  exact mul_pos (div_pos two_pos hr') (pow_pos hq 2)

theorem ErCoeff_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < ErCoeff r k := by
  have h1 : (0 : ℝ) < risingFact (1 / 2) k := risingFact_pos (by norm_num) k
  have h2 : (0 : ℝ) < (r : ℝ) / 2 + 1 := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  have h3 : (0 : ℝ) < risingFact ((r : ℝ) / 2 + 1) k := risingFact_pos h2 k
  have h4 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  unfold ErCoeff
  exact div_pos (mul_pos (Cr_pos hr) (pow_pos h1 2)) (mul_pos h3 h4)

theorem ErCoeff_nonneg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k :=
  (ErCoeff_pos hr k).le

/-! ### The bound `(3/2)_k = (2k+1)(1/2)_k ≤ (r/2+1)_k` -/

theorem three_halves_risingFact (k : ℕ) :
    risingFact (3 / 2) k = (2 * (k : ℝ) + 1) * risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
    rw [risingFact_succ, risingFact_succ, ih]
    push_cast
    ring

theorem three_halves_le_risingFact {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    risingFact (3 / 2) k ≤ risingFact ((r : ℝ) / 2 + 1) k := by
  have h32 : (3 / 2 : ℝ) ≤ (r : ℝ) / 2 + 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  unfold risingFact
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith

/-! ### The bound `(1/2)_k / k! ≤ 1/√(k+1)` -/

theorem half_fact_succ (k : ℕ) :
    risingFact (1 / 2) (k + 1) / (((k + 1).factorial : ℕ) : ℝ)
      = risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ) * ((k : ℝ) + 1 / 2) / ((k : ℝ) + 1) := by
  rw [risingFact_succ, Nat.factorial_succ]
  push_cast
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos k
    positivity
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem half_sq_bound (k : ℕ) :
    (risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ)) ^ 2 * ((k : ℝ) + 1) ≤ 1 := by
  induction k with
  | zero => norm_num [risingFact]
  | succ n ih =>
    rw [half_fact_succ]
    have hcast : (((n + 1 : ℕ)) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : ((n : ℝ) + 1 / 2) ^ 2 * ((n : ℝ) + 2) ≤ ((n : ℝ) + 1) ^ 3 := by nlinarith
    have hmul : (risingFact (1 / 2) n / ((n.factorial : ℕ) : ℝ)) ^ 2 * ((n : ℝ) + 1) *
        (((n : ℝ) + 1 / 2) ^ 2 * ((n : ℝ) + 2)) ≤
        ((n : ℝ) + 1 / 2) ^ 2 * ((n : ℝ) + 2) := by
      have h0 : (0 : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 * ((n : ℝ) + 2) := by positivity
      have h := mul_le_mul_of_nonneg_right ih h0
      linarith [h]
    have key : (risingFact (1 / 2) n / ((n.factorial : ℕ) : ℝ)) ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 *
        ((n : ℝ) + 2) ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [hmul, h2, hpos]
    have e : (risingFact (1 / 2) n / ((n.factorial : ℕ) : ℝ) * ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) ^ 2 *
          ((n : ℝ) + 2)
        = (risingFact (1 / 2) n / ((n.factorial : ℕ) : ℝ)) ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 *
          ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 := by
      field_simp
    rw [e, div_le_one (by positivity)]
    exact key

theorem half_mul_sqrt_le (k : ℕ) :
    risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ) * Real.sqrt ((k : ℝ) + 1) ≤ 1 := by
  have hq : 0 ≤ risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < risingFact (1 / 2) k := risingFact_pos (by norm_num) k
    have h2 : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos k
    positivity
  calc risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ) * Real.sqrt ((k : ℝ) + 1)
      = Real.sqrt ((risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ)) ^ 2) *
        Real.sqrt ((k : ℝ) + 1) := by rw [Real.sqrt_sq hq]
    _ = Real.sqrt ((risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ)) ^ 2 * ((k : ℝ) + 1)) := by
        rw [Real.sqrt_mul (by positivity)]
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (half_sq_bound k)
    _ = 1 := Real.sqrt_one

/-! ### The coefficient bound -/

theorem ErCoeff_le_rpow {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    ErCoeff r k ≤ Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
  have hA : 0 < risingFact (1 / 2) k := risingFact_pos (by norm_num) k
  have hk : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hB : 0 < risingFact ((r : ℝ) / 2 + 1) k := risingFact_pos (by linarith) k
  have hAB : risingFact (1 / 2) k * (2 * (k : ℝ) + 1) ≤ risingFact ((r : ℝ) / 2 + 1) k := by
    rw [mul_comm, ← three_halves_risingFact k]
    exact three_halves_le_risingFact hr k
  -- `A^2 / (B k!) ≤ A / ((2k+1) k!)`
  have step1 : risingFact (1 / 2) k ^ 2 / (risingFact ((r : ℝ) / 2 + 1) k * ((k.factorial : ℕ) : ℝ))
      ≤ risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : risingFact (1 / 2) k * (2 * (k : ℝ) + 1) * (risingFact (1 / 2) k * ((k.factorial : ℕ) : ℝ))
        ≤ risingFact ((r : ℝ) / 2 + 1) k * (risingFact (1 / 2) k * ((k.factorial : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hAB (by positivity)
    nlinarith [h1]
  -- `A/k! ≤ 1/√(k+1)`
  have hqle : risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ) ≤ 1 / Real.sqrt ((k : ℝ) + 1) := by
    have hpos : (0 : ℝ) < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    rw [le_div_iff₀ hpos]
    simpa using half_mul_sqrt_le k
  have step2 : risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ))
      ≤ 1 / (Real.sqrt ((k : ℝ) + 1) * (2 * (k : ℝ) + 1)) := by
    have h1 : risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ))
        = risingFact (1 / 2) k / ((k.factorial : ℕ) : ℝ) / (2 * (k : ℝ) + 1) := by
      field_simp
    have h2 : (1 : ℝ) / (Real.sqrt ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))
        = (1 / Real.sqrt ((k : ℝ) + 1)) / (2 * (k : ℝ) + 1) := by
      field_simp
    rw [h1, h2]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hqle
  -- `1/(√(k+1)(2k+1)) ≤ (k+1)^{-3/2}`
  have step3 : (1 : ℝ) / (Real.sqrt ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))
      ≤ ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
    have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hs : (0 : ℝ) < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have h32 : ((k : ℝ) + 1) ^ ((3 : ℝ) / 2) = ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) := by
      have hsplit : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
      rw [hsplit, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hneg : ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) = (((k : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ := by
      have h3 : (-(3 / 2) : ℝ) = -((3 : ℝ) / 2) := by norm_num
      rw [h3, Real.rpow_neg hx.le]
    rw [hneg, h32, one_div, inv_le_inv₀ (by positivity) (by positivity)]
    have key : ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) := by
      calc ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)
          = Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) := by ring
        _ ≤ Real.sqrt ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hs.le
            linarith
    exact key
  have hCr : 0 < Cr r := Cr_pos hr
  have hfinal : risingFact (1 / 2) k ^ 2 / (risingFact ((r : ℝ) / 2 + 1) k * ((k.factorial : ℕ) : ℝ))
      ≤ ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
    calc risingFact (1 / 2) k ^ 2 / (risingFact ((r : ℝ) / 2 + 1) k * ((k.factorial : ℕ) : ℝ))
        ≤ risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ)) := step1
      _ ≤ 1 / (Real.sqrt ((k : ℝ) + 1) * (2 * (k : ℝ) + 1)) := step2
      _ ≤ ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := step3
  calc ErCoeff r k
      = Cr r * (risingFact (1 / 2) k ^ 2 /
          (risingFact ((r : ℝ) / 2 + 1) k * ((k.factorial : ℕ) : ℝ))) := by
        unfold ErCoeff
        ring
    _ ≤ Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hfinal hCr.le

theorem summable_ErCoeff_rpow :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ)) := by
  have hf : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hf1 : Summable (fun k : ℕ => (((k + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (summable_nat_add_iff 1).2 hf
  refine hf1.congr (fun k => ?_)
  push_cast
  ring_nf

theorem summable_ErCoeff {r : ℕ} (hr : 1 ≤ r) : Summable (fun k : ℕ => ErCoeff r k) := by
  have hsum : Summable (fun k : ℕ => Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ)) :=
    summable_ErCoeff_rpow.mul_left (Cr r)
  exact Summable.of_nonneg_of_le (fun k => ErCoeff_nonneg hr k)
    (fun k => ErCoeff_le_rpow hr k) hsum

end Grothendieck

/-!
# `E_r` is a continuous, strictly increasing odd function on `[-1,1]`

Consequently `ErInv = Function.invFunOn (Er r) (Icc (-1) 1)` is a genuine inverse of `E_r`
on the range `[-E_r(1), E_r(1)]`, which is what the construction of Lemma 4.1 needs.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

/-! ### Summability of the defining series on `[-1,1]` -/

theorem Er_summable {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) :
    Summable fun k : ℕ => ErCoeff r k * t ^ (2 * k + 1) := by
  have hbound : ∀ k : ℕ,
      |ErCoeff r k * t ^ (2 * k + 1)| ≤ Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
    intro k
    have h1 : |t ^ (2 * k + 1)| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg t) (by simpa using ht)
    calc |ErCoeff r k * t ^ (2 * k + 1)| = ErCoeff r k * |t ^ (2 * k + 1)| := by
          rw [abs_mul, abs_of_pos (ErCoeff_pos hr k)]
      _ ≤ ErCoeff r k * 1 := mul_le_mul_of_nonneg_left h1 (ErCoeff_pos hr k).le
      _ = ErCoeff r k := mul_one _
      _ ≤ Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) := ErCoeff_le_rpow hr k
  have hsum : Summable fun k : ℕ => Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ) :=
    summable_ErCoeff_rpow.mul_left (Cr r)
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbound hsum |>.of_abs

theorem Er_eq_tsum (r : ℕ) (t : ℝ) :
    Er r t = ∑' k : ℕ, ErCoeff r k * t ^ (2 * k + 1) := rfl

theorem Er_zero (r : ℕ) : Er r 0 = 0 := by
  rw [Er_eq_tsum]
  simp

theorem Er_odd {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) : Er r (-t) = -Er r t := by
  have h1 : Summable fun k : ℕ => ErCoeff r k * t ^ (2 * k + 1) := Er_summable hr ht
  calc Er r (-t) = ∑' k : ℕ, -(ErCoeff r k * t ^ (2 * k + 1)) := by
        rw [Er_eq_tsum]
        refine tsum_congr fun k => ?_
        have hod : Odd (2 * k + 1) := ⟨k, by ring⟩
        rw [Odd.neg_pow hod]
        ring
    _ = -∑' k : ℕ, ErCoeff r k * t ^ (2 * k + 1) := tsum_neg
    _ = -Er r t := by rw [Er_eq_tsum]

theorem Er_continuousOn {r : ℕ} (hr : 1 ≤ r) :
    ContinuousOn (Er r) (Set.Icc (-1 : ℝ) 1) := by
  have hcont : ∀ k : ℕ, ContinuousOn (fun t : ℝ => ErCoeff r k * t ^ (2 * k + 1))
      (Set.Icc (-1 : ℝ) 1) :=
    fun k => (continuous_const.mul (continuous_pow _)).continuousOn
  refine continuousOn_tsum (u := fun k : ℕ => Cr r * ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ))
    hcont (summable_ErCoeff_rpow.mul_left (Cr r)) ?_
  intro n x hx
  have hx1 : |x| ≤ 1 := abs_le.2 hx
  have h1 : |x ^ (2 * n + 1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (by simpa using hx1)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (ErCoeff_pos hr n)]
  calc ErCoeff r n * |x ^ (2 * n + 1)| ≤ ErCoeff r n * 1 :=
        mul_le_mul_of_nonneg_left h1 (ErCoeff_pos hr n).le
    _ = ErCoeff r n := mul_one _
    _ ≤ Cr r * ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ) := ErCoeff_le_rpow hr n

/-! ### Strict monotonicity -/

theorem Er_strictMonoOn_nonneg {r : ℕ} (hr : 1 ≤ r) :
    StrictMonoOn (Er r) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx1 : |x| ≤ 1 := abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have hy1 : |y| ≤ 1 := abs_le.2 ⟨by linarith [hy.1], hy.2⟩
  have hsx := Er_summable hr hx1
  have hsy := Er_summable hr hy1
  have hterm : ∀ k : ℕ,
      0 ≤ ErCoeff r k * y ^ (2 * k + 1) - ErCoeff r k * x ^ (2 * k + 1) := by
    intro k
    have hp : x ^ (2 * k + 1) ≤ y ^ (2 * k + 1) := pow_le_pow_left₀ hx.1 hxy.le _
    have ha : 0 ≤ ErCoeff r k := ErCoeff_nonneg hr k
    nlinarith
  have hsub : Summable fun k : ℕ =>
      (ErCoeff r k * y ^ (2 * k + 1) - ErCoeff r k * x ^ (2 * k + 1)) := hsy.sub hsx
  have hle := hsub.sum_le_tsum ({0} : Finset ℕ) (fun k _ => hterm k)
  have h0 : 0 < ∑ k ∈ ({0} : Finset ℕ),
      (ErCoeff r k * y ^ (2 * k + 1) - ErCoeff r k * x ^ (2 * k + 1)) := by
    rw [Finset.sum_singleton]
    have hc : 0 < ErCoeff r 0 := ErCoeff_pos hr 0
    have : (2 * 0 + 1) = 1 := by norm_num
    rw [this, pow_one, pow_one]
    nlinarith
  have hpos : 0 < ∑' k : ℕ,
      (ErCoeff r k * y ^ (2 * k + 1) - ErCoeff r k * x ^ (2 * k + 1)) :=
    lt_of_lt_of_le h0 hle
  have hsplit : Er r y - Er r x = ∑' k : ℕ,
      (ErCoeff r k * y ^ (2 * k + 1) - ErCoeff r k * x ^ (2 * k + 1)) := by
    rw [Er_eq_tsum, Er_eq_tsum, ← hsy.tsum_sub hsx]
  linarith [hpos, hsplit]

theorem Er_strictMonoOn {r : ℕ} (hr : 1 ≤ r) :
    StrictMonoOn (Er r) (Set.Icc (-1 : ℝ) 1) := by
  have hmono := Er_strictMonoOn_nonneg hr
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  intro x hx y hy hxy
  have hodd : ∀ t : ℝ, |t| ≤ 1 → Er r (-t) = -Er r t := fun t ht => Er_odd hr ht
  have hxm1 : |x| ≤ 1 := abs_le.2 hx
  have hym1 : |y| ≤ 1 := abs_le.2 hy
  rcases lt_or_ge x 0 with hxneg | hxnonneg
  · rcases lt_or_ge y 0 with hyneg | hynonneg
    · -- both negative: reflect
      have hlt : -y < -x := by linarith
      have hy' : (-y) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hy.1]⟩
      have hx' : (-x) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
      have h := hmono hy' hx' hlt
      have e1 : Er r x = -Er r (-x) := by
        have h2 := hodd (-x) (by rw [abs_neg]; exact hxm1)
        simpa using h2
      have e2 : Er r y = -Er r (-y) := by
        have h2 := hodd (-y) (by rw [abs_neg]; exact hym1)
        simpa using h2
      rw [e1, e2]
      linarith
    · -- x < 0 ≤ y
      have hpx : 0 < Er r (-x) := by
        have hmem : (0 : ℝ) < -x := by linarith
        have hmem' : (-x) ∈ Set.Icc (0 : ℝ) 1 := ⟨hmem.le, by linarith [hx.1]⟩
        have h := hmono hmem0 hmem' hmem
        rwa [Er_zero] at h
      have e1 : Er r x = -Er r (-x) := by
        have h2 := hodd (-x) (by rw [abs_neg]; exact hxm1)
        simpa using h2
      rcases eq_or_lt_of_le hynonneg with hy0 | hypos
      · rw [← hy0, Er_zero]
        rw [e1]
        linarith
      · have hpy : 0 < Er r y := by
          have hmem' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hypos.le, hy.2⟩
          have h := hmono hmem0 hmem' hypos
          rwa [Er_zero] at h
        rw [e1]
        linarith
  · -- 0 ≤ x < y
    exact hmono ⟨hxnonneg, hx.2⟩ ⟨by linarith, hy.2⟩ hxy

theorem Er_injOn {r : ℕ} (hr : 1 ≤ r) : Set.InjOn (Er r) (Set.Icc (-1 : ℝ) 1) :=
  (Er_strictMonoOn hr).injOn

/-! ### Value at `1` and the range -/

theorem Er_one_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Er r 1 := by
  have hs : Summable fun k : ℕ => ErCoeff r k * (1 : ℝ) ^ (2 * k + 1) :=
    Er_summable hr (by norm_num)
  have hle : ∑ k ∈ ({0} : Finset ℕ), ErCoeff r k * (1 : ℝ) ^ (2 * k + 1) ≤
      ∑' k : ℕ, ErCoeff r k * (1 : ℝ) ^ (2 * k + 1) :=
    hs.sum_le_tsum _ (fun k _ => mul_nonneg (ErCoeff_nonneg hr k) (by positivity))
  have h0 : 0 < ∑ k ∈ ({0} : Finset ℕ), ErCoeff r k * (1 : ℝ) ^ (2 * k + 1) := by
    rw [Finset.sum_singleton]
    have hc : 0 < ErCoeff r 0 := ErCoeff_pos hr 0
    have h1 : ((1 : ℝ) ^ (2 * 0 + 1)) = 1 := by norm_num
    rw [h1, mul_one]
    exact hc
  have h : 0 < ∑' k : ℕ, ErCoeff r k * (1 : ℝ) ^ (2 * k + 1) := lt_of_lt_of_le h0 hle
  simpa [Er] using h

theorem Er_neg_one {r : ℕ} (hr : 1 ≤ r) : Er r (-1) = -Er r 1 :=
  Er_odd hr (by norm_num)

/-- Every `y` with `|y| ≤ E_r(1)` is a value of `E_r` on `[-1,1]`. -/
theorem Er_mem_range {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : |y| ≤ Er r 1) :
    ∃ a ∈ Set.Icc (-1 : ℝ) 1, Er r a = y := by
  have hcont := Er_continuousOn hr
  have hpos : 0 < Er r 1 := Er_one_pos hr
  have hcontsub : ContinuousOn (Er r) (Set.Icc (0 : ℝ) 1) :=
    hcont.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  have hcontsub' : ContinuousOn (Er r) (Set.Icc (-1 : ℝ) 0) :=
    hcont.mono (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)
  rcases abs_le.1 hy with ⟨hy1, hy2⟩
  rcases le_or_gt 0 y with hy0 | hy0
  · have hmem : y ∈ Set.Icc (Er r 0) (Er r 1) := by
      rw [Er_zero]
      exact ⟨hy0, hy2⟩
    obtain ⟨a, ha, hay⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcontsub hmem
    exact ⟨a, ⟨by linarith [ha.1], ha.2⟩, hay⟩
  · have hy0' : y ≤ 0 := hy0.le
    have hmem : y ∈ Set.Icc (Er r (-1)) (Er r 0) := by
      rw [Er_zero, Er_neg_one hr]
      exact ⟨by linarith, hy0'⟩
    obtain ⟨a, ha, hay⟩ := intermediate_value_Icc (by norm_num : (-1:ℝ) ≤ 0) hcontsub' hmem
    exact ⟨a, ⟨ha.1, by linarith [ha.2]⟩, hay⟩

/-! ### The inverse identities for `ErInv` -/

theorem Er_ErInv {r : ℕ} {y : ℝ} (hy : ∃ a ∈ Set.Icc (-1 : ℝ) 1, Er r a = y) :
    Er r (ErInv r y) = y :=
  Function.invFunOn_eq hy

theorem ErInv_Er {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ErInv r (Er r x) = x :=
  (Er_injOn hr).leftInvOn_invFunOn hx

theorem ErInv_mem {r : ℕ} {y : ℝ} (hy : ∃ a ∈ Set.Icc (-1 : ℝ) 1, Er r a = y) :
    ErInv r y ∈ Set.Icc (-1 : ℝ) 1 :=
  Function.invFunOn_mem hy

/-- `ErInv` is the inverse of `E_r` on the range interval `[-E_r(1), E_r(1)]`. -/
theorem Er_ErInv_of_abs_le {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : |y| ≤ Er r 1) :
    Er r (ErInv r y) = y :=
  Er_ErInv (Er_mem_range hr hy)

theorem additive_ErInv_abs_le {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : |y| ≤ Er r 1) :
    |ErInv r y| ≤ 1 := by
  have hmem := ErInv_mem (Er_mem_range hr hy)
  exact abs_le.2 hmem

end Grothendieck

/-!
# Tensor powers and the signed feature map

Elementary Hilbert-space ingredients of the construction of Lemma 4.1 of
Briët–de Oliveira Filho–Vallentin: the `j`-fold tensor power of a vector (realised as a
function on `Fin j → V`, whose inner products are powers of the inner product), and the
signed combination of two tensor powers that turns the *alternating* power series for
`E_r⁻¹` into a genuine inner product.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `j`-fold tensor power of `x`, realised as the function `φ ↦ ∏ i, x (φ i)` on
`Fin j → V`. -/
def tensPow (j : ℕ) (x : EuclideanSpace ℝ V) : EuclideanSpace ℝ (Fin j → V) :=
  WithLp.toLp 2 fun φ => ∏ i : Fin j, x (φ i)

theorem tensPow_apply (j : ℕ) (x : EuclideanSpace ℝ V) (φ : Fin j → V) :
    tensPow j x φ = ∏ i : Fin j, x (φ i) := rfl

theorem inner_eq_sum (x y : EuclideanSpace ℝ V) : inner ℝ x y = ∑ v, y v * x v := by
  rw [PiLp.inner_apply]
  simp

/-- The inner product of two tensor powers is the corresponding power of the inner
product. -/
theorem inner_tensPow (j : ℕ) (x y : EuclideanSpace ℝ V) :
    inner ℝ (tensPow j x) (tensPow j y) = (inner ℝ x y) ^ j := by
  rw [inner_eq_sum (tensPow j x) (tensPow j y), inner_eq_sum x y, Fintype.sum_pow]
  refine Finset.sum_congr rfl fun φ _ => ?_
  simp only [tensPow_apply, Finset.prod_mul_distrib]

/-! ### The signed coefficients -/

theorem max_sub_max_neg (b : ℝ) : max b 0 - max (-b) 0 = b := by
  rw [max_def, max_def]
  split_ifs <;> linarith

theorem max_add_max_neg (b : ℝ) : max b 0 + max (-b) 0 = |b| := by
  rw [max_def, max_def]
  split_ifs with h1 h2 h2
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith
  · linarith

/-- `a k ² - c k ² = b_{2k+1} β^{2k+1}` and `a k ² + c k ² = |b_{2k+1}| β^{2k+1}`. -/
def aCoef (r : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (β ^ (2 * k + 1) * max (invCoeff r (2 * k + 1)) 0)

def cCoef (r : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (β ^ (2 * k + 1) * max (-(invCoeff r (2 * k + 1))) 0)

theorem aCoef_sq {r : ℕ} {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    aCoef r β k ^ 2 = β ^ (2 * k + 1) * max (invCoeff r (2 * k + 1)) 0 := by
  rw [aCoef, Real.sq_sqrt]
  positivity

theorem cCoef_sq {r : ℕ} {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    cCoef r β k ^ 2 = β ^ (2 * k + 1) * max (-(invCoeff r (2 * k + 1))) 0 := by
  rw [cCoef, Real.sq_sqrt]
  positivity

theorem aCoef_sq_sub_cCoef_sq {r : ℕ} {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    aCoef r β k ^ 2 - cCoef r β k ^ 2 = β ^ (2 * k + 1) * invCoeff r (2 * k + 1) := by
  rw [aCoef_sq hβ, cCoef_sq hβ, ← mul_sub, max_sub_max_neg]

theorem aCoef_sq_add_cCoef_sq {r : ℕ} {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    aCoef r β k ^ 2 + cCoef r β k ^ 2 = β ^ (2 * k + 1) * |invCoeff r (2 * k + 1)| := by
  rw [aCoef_sq hβ, cCoef_sq hβ, ← mul_add, max_add_max_neg]

/-! ### The signed feature vector -/

/-- The signed feature vector of the ordered pair `(p + q, p - q)`: the `inl` block holds
`a_k (p+q) ⊗ x^{⊗(2k+1)}`, the `inr` block holds `c_k (p-q) ⊗ x^{⊗(2k+1)}`. -/
def feat (r : ℕ) (β : ℝ) (p q : V → ℝ) (x : EuclideanSpace ℝ V) (k : ℕ) :
    EuclideanSpace ℝ (Sum (V × (Fin (2 * k + 1) → V)) (V × (Fin (2 * k + 1) → V))) :=
  WithLp.toLp 2 fun w =>
    match w with
    | Sum.inl (v, φ) => aCoef r β k * (p v + q v) * ∏ i : Fin (2 * k + 1), x (φ i)
    | Sum.inr (v, φ) => cCoef r β k * (p v - q v) * ∏ i : Fin (2 * k + 1), x (φ i)

@[simp]
theorem feat_inl (r : ℕ) (β : ℝ) (p q : V → ℝ) (x : EuclideanSpace ℝ V) (k : ℕ)
    (v : V) (φ : Fin (2 * k + 1) → V) :
    feat r β p q x k (Sum.inl (v, φ)) =
      aCoef r β k * (p v + q v) * ∏ i : Fin (2 * k + 1), x (φ i) := rfl

@[simp]
theorem feat_inr (r : ℕ) (β : ℝ) (p q : V → ℝ) (x : EuclideanSpace ℝ V) (k : ℕ)
    (v : V) (φ : Fin (2 * k + 1) → V) :
    feat r β p q x k (Sum.inr (v, φ)) =
      cCoef r β k * (p v - q v) * ∏ i : Fin (2 * k + 1), x (φ i) := rfl

/-- The inner product of two signed feature vectors. -/
theorem inner_feat {r : ℕ} {β : ℝ} (hβ : 0 ≤ β) (k : ℕ)
    (p q p' q' : V → ℝ) (x y : EuclideanSpace ℝ V) :
    inner ℝ (feat r β p q x k) (feat r β p' q' y k) =
      aCoef r β k ^ 2 * (∑ v, (p v + q v) * (p' v + q' v)) * (inner ℝ x y) ^ (2 * k + 1) +
        cCoef r β k ^ 2 * (∑ v, (p v - q v) * (p' v - q' v)) *
          (inner ℝ x y) ^ (2 * k + 1) := by
  rw [inner_eq_sum (feat r β p q x k) (feat r β p' q' y k), Fintype.sum_sum_type]
  simp only [feat_inl, feat_inr, Fintype.sum_prod_type]
  have key : ∀ (c : ℝ) (U W : V → ℝ),
      (∑ v : V, ∑ φ : Fin (2 * k + 1) → V,
          (c * W v * ∏ i : Fin (2 * k + 1), y (φ i)) *
            (c * U v * ∏ i : Fin (2 * k + 1), x (φ i)))
        = c ^ 2 * (∑ v, U v * W v) * (inner ℝ x y) ^ (2 * k + 1) := by
    intro c U W
    have hU : (∑ v : V, (c * W v) * (c * U v)) = c ^ 2 * (∑ v, U v * W v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    have hP : (∑ φ : Fin (2 * k + 1) → V,
        (∏ i : Fin (2 * k + 1), y (φ i)) * (∏ i : Fin (2 * k + 1), x (φ i)))
        = (inner ℝ x y) ^ (2 * k + 1) := by
      rw [← inner_tensPow (2 * k + 1) x y, inner_eq_sum]
      refine Finset.sum_congr rfl fun φ _ => ?_
      rw [tensPow_apply, tensPow_apply]
    calc (∑ v : V, ∑ φ : Fin (2 * k + 1) → V,
            (c * W v * ∏ i : Fin (2 * k + 1), y (φ i)) *
              (c * U v * ∏ i : Fin (2 * k + 1), x (φ i)))
        = ∑ v : V, ∑ φ : Fin (2 * k + 1) → V,
            ((c * W v) * (c * U v)) *
              ((∏ i : Fin (2 * k + 1), y (φ i)) * (∏ i : Fin (2 * k + 1), x (φ i))) := by
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun φ _ => by ring
      _ = (∑ v : V, (c * W v) * (c * U v)) *
            (∑ φ : Fin (2 * k + 1) → V,
              (∏ i : Fin (2 * k + 1), y (φ i)) * (∏ i : Fin (2 * k + 1), x (φ i))) := by
          rw [Fintype.sum_mul_sum]
      _ = c ^ 2 * (∑ v, U v * W v) * (inner ℝ x y) ^ (2 * k + 1) := by rw [hU, hP]
  rw [key (aCoef r β k) (fun v => p v + q v) (fun v => p' v + q' v),
    key (cCoef r β k) (fun v => p v - q v) (fun v => p' v - q' v)]

end Grothendieck

/-!
# `β(r,G)` satisfies the defining equation (4.2)

`beta r G` is defined in the definition layer as the infimum of the `t ≥ 0` for which
`∑ k, |b_{2k+1}| t^{2k+1} ≥ 1/(ϑ(G)-1)`.  We show that, once the series is known to
converge just to the right of `β(r,G)` (which is what Proposition 4.2/Theorem 3.1 of the
paper provide) and the defining set is nonempty, the infimum is where the series *equals*
`1/(ϑ(G)-1)`:

`betaSeries r (beta r G) = 1/(ϑ(G)-1)`.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem betaSeries_zero (r : ℕ) : betaSeries r 0 = 0 := by
  rw [betaSeries]
  simp

/-- **Equation (4.2)**: the `sInf`-definition of `β(r,G)` agrees with the paper's equation,
granting that the defining set is nonempty and that the series converges to the right of
`β(r,G)`. -/
theorem betaSeries_beta_eq (r : ℕ) (G : SimpleGraph V) (hϑ : 2 ≤ thetaComplement G)
    (hne : ∃ t : ℝ, 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t)
    (hsum : ∀ t : ℝ, beta r G < t →
      Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1)) :
    betaSeries r (beta r G) = 1 / (thetaComplement G - 1) := by
  classical
  have hlampos : 0 < thetaComplement G - 1 := by linarith
  have hcpos : 1 / (thetaComplement G - 1) > 0 := by positivity
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t} with hS
  have hSne : S.Nonempty := hne
  have hβdef : beta r G = sInf S := rfl
  have hβ_le : ∀ t ∈ S, beta r G ≤ t := by
    intro t ht
    rw [hβdef]
    exact csInf_le ⟨0, fun y hy => hy.1⟩ ht
  have hβnn : 0 ≤ beta r G := by
    rw [hβdef]
    exact Real.sInf_nonneg fun t ht => ht.1
  -- summability at `β + 1`, hence domination everywhere below
  have hsum1 : Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * (beta r G + 1) ^ (2 * k + 1) :=
    hsum _ (by linarith)
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ beta r G + 1 →
      betaSeries r s ≤ betaSeries r t := by
    intro s t hs hst ht1
    have hsum_t : Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1) := by
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (le_trans hs hst) _)) (fun k => ?_) hsum1
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans hs hst) ht1 _) (abs_nonneg _)
    have hsum_s : Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * s ^ (2 * k + 1) := by
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hs _)) (fun k => ?_) hsum_t
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst _) (abs_nonneg _)
    exact hsum_s.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst _) (abs_nonneg _)) hsum_t
  -- continuity on `[0, β+1]`
  have hcont : ContinuousOn (betaSeries r) (Set.Icc (0:ℝ) (beta r G + 1)) := by
    refine continuousOn_tsum (u := fun k : ℕ =>
      |invCoeff r (2 * k + 1)| * (beta r G + 1) ^ (2 * k + 1)) ?_ hsum1 ?_
    · intro k
      exact (continuous_const.mul (continuous_pow _)).continuousOn
    · intro k x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_pow, abs_of_nonneg hx.1]
      exact pow_le_pow_left₀ hx.1 hx.2 _
  have hδ_of : ∀ (x : ℝ), x ∈ Set.Icc (0:ℝ) (beta r G + 1) → ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, ∀ y ∈ Set.Icc (0:ℝ) (beta r G + 1), |y - x| < δ →
        |betaSeries r y - betaSeries r x| < ε := by
    intro x hx ε hε
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.1 (hcont x hx)) ε hε
    exact ⟨δ, hδpos, fun y hy hxy => by
      have := hδ hy (by simpa [Real.dist_eq] using hxy)
      simpa [Real.dist_eq] using this⟩
  -- the interval `[0, β+1]` contains the relevant points
  have hβmem : beta r G ∈ Set.Icc (0:ℝ) (beta r G + 1) := ⟨hβnn, by linarith⟩
  refine le_antisymm ?_ ?_
  swap
  · by_contra hcon
    have hcon' : betaSeries r (beta r G) < 1 / (thetaComplement G - 1) := not_le.1 hcon
    have hεpos : 0 < 1 / (thetaComplement G - 1) - betaSeries r (beta r G) := by linarith
    obtain ⟨δ, hδpos, hδ⟩ := hδ_of (beta r G) hβmem _ hεpos
    set y0 : ℝ := beta r G + min (δ / 2) (1 / 2) with hy0
    have hminpos : 0 < min (δ / 2) (1 / 2) := by
      exact lt_min (by linarith : (0:ℝ) < δ / 2) (by norm_num : (0:ℝ) < 1 / 2)
    have hminleft : min (δ / 2) (1 / 2) ≤ δ / 2 := min_le_left _ _
    have hminright : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hy0mem : y0 ∈ Set.Icc (0:ℝ) (beta r G + 1) := by
      refine ⟨by rw [hy0]; linarith, by rw [hy0]; linarith⟩
    have hy0dist : |y0 - beta r G| < δ := by
      have h1 : y0 - beta r G = min (δ / 2) (1 / 2) := by rw [hy0]; ring
      rw [h1, abs_of_pos hminpos]
      linarith
    have hy0lt : betaSeries r y0 < 1 / (thetaComplement G - 1) := by
      have h1 := hδ y0 hy0mem hy0dist
      rw [abs_lt] at h1
      linarith [h1.2]
    have hbdd : ∀ t ∈ S, y0 ≤ t := by
      intro t ht
      by_contra hlt
      push_neg at hlt
      rcases le_or_gt t (beta r G) with h1 | h1
      · have h2 : betaSeries r t ≤ betaSeries r (beta r G) := hmono t (beta r G) ht.1 h1 (by linarith)
        linarith [ht.2]
      · have h2 : betaSeries r t ≤ betaSeries r y0 :=
          hmono t y0 (le_trans hβnn h1.le) hlt.le (by rw [hy0]; linarith)
        linarith [ht.2]
    have h3 : y0 ≤ beta r G := by
      rw [hβdef]
      exact le_csInf hSne hbdd
    rw [hy0] at h3
    linarith
  · by_contra hcon
    have hcon' : 1 / (thetaComplement G - 1) < betaSeries r (beta r G) := not_le.1 hcon
    have hεpos : 0 < betaSeries r (beta r G) - 1 / (thetaComplement G - 1) := by linarith
    obtain ⟨δ, hδpos, hδ⟩ := hδ_of (beta r G) hβmem _ hεpos
    have hβpos : 0 < beta r G := by
      rcases eq_or_lt_of_le hβnn with h | h
      · have hz : betaSeries r (beta r G) = 0 := by rw [← h, betaSeries_zero]
        rw [hz] at hcon'
        linarith
      · exact h
    set y0 : ℝ := beta r G - min (δ / 2) (beta r G / 2) with hy0
    have hminpos : 0 < min (δ / 2) (beta r G / 2) := by
      exact lt_min (by linarith : (0:ℝ) < δ / 2) (by linarith : (0:ℝ) < beta r G / 2)
    have hminleft : min (δ / 2) (beta r G / 2) ≤ δ / 2 := min_le_left _ _
    have hminright : min (δ / 2) (beta r G / 2) ≤ beta r G / 2 := min_le_right _ _
    have hy0mem : y0 ∈ Set.Icc (0:ℝ) (beta r G + 1) := by
      refine ⟨by rw [hy0]; linarith, by rw [hy0]; linarith⟩
    have hy0dist : |y0 - beta r G| < δ := by
      have h1 : y0 - beta r G = - min (δ / 2) (beta r G / 2) := by rw [hy0]; ring
      rw [h1, abs_neg, abs_of_pos hminpos]
      linarith
    have hy0gt : 1 / (thetaComplement G - 1) < betaSeries r y0 := by
      have h1 := hδ y0 hy0mem hy0dist
      rw [abs_lt] at h1
      linarith [h1.1]
    have hy0S : y0 ∈ S := ⟨by rw [hy0]; linarith, le_of_lt hy0gt⟩
    have := hβ_le y0 hy0S
    rw [hy0] at this
    linarith

end Grothendieck

/-!
# Step (ii) of Lemma 4.1: vectors from an optimal solution of the theta program

Given `Z ⪰ 0` with `Z u u = ϑ(G)-1` and `Z u v = -1` across edges (`λ := ϑ(G)-1`), we build
`s, t` in `R^{2|V|+1}` with

`‖s u‖² = ‖t u‖² = (ϑ(G)-1)/2`, `⟨s u, t u⟩ = 0`,
`⟨s u, s v⟩ = ⟨t u, t v⟩ = 0` and `⟨s u, t v⟩ = ⟨t u, s v⟩ = 1/2` for every edge `uv`.

Explicitly, if `z u` are Gram vectors of `Z` and `a² = (λ-1)/(4(λ+1))`, `b = 1/2`,
`c² = λ/(2(λ+1))`, then `s u = (a z u, b z u, c)` and `t u = (a z u, -b z u, c)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open scoped BigOperators Real
open MatrixOrder

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem inner_eucl_sum {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    inner ℝ x y = ∑ i, y i * x i := by
  rw [PiLp.inner_apply]
  simp

theorem real_inner_swap' (a b : ℝ) : inner ℝ a b = b * a := by simp

/-- Every positive semidefinite real matrix is the Gram matrix of vectors in `R^V`. -/
theorem posSemidef_exists_gram {M : Matrix V V ℝ} (hM : M.PosSemidef) :
    ∃ z : V → EuclideanSpace ℝ V, ∀ u v, inner ℝ (z u) (z v) = M u v := by
  have hnn : (0 : Matrix V V ℝ) ≤ M := hM.nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnn
  refine ⟨fun u => WithLp.toLp 2 (fun w => B w u), fun u v => ?_⟩
  have hMuv : M u v = (star B * B) u v := by rw [hB]
  rw [hMuv, Matrix.mul_apply, PiLp.inner_apply]
  simp only [Matrix.star_apply, star_trivial, real_inner_swap']
  exact Finset.sum_congr rfl fun w _ => by ring

/-- Coefficient `a = √((λ-1)/(4(λ+1)))`. -/
def coefA (lam : ℝ) : ℝ := Real.sqrt (max ((lam - 1) / (4 * (lam + 1))) 0)

/-- Coefficient `c = √(λ/(2(λ+1)))`. -/
def coefC (lam : ℝ) : ℝ := Real.sqrt (max (lam / (2 * (lam + 1))) 0)

theorem coefA_sq {lam : ℝ} (h : 1 ≤ lam) : coefA lam ^ 2 = (lam - 1) / (4 * (lam + 1)) := by
  have h1 : (0:ℝ) ≤ (lam - 1) / (4 * (lam + 1)) :=
    div_nonneg (by linarith) (by linarith)
  rw [coefA, Real.sq_sqrt (le_max_right _ _), max_eq_left h1]

theorem coefC_sq {lam : ℝ} (h : 1 ≤ lam) : coefC lam ^ 2 = lam / (2 * (lam + 1)) := by
  have h1 : (0:ℝ) ≤ lam / (2 * (lam + 1)) := div_nonneg (by linarith) (by linarith)
  rw [coefC, Real.sq_sqrt (le_max_right _ _), max_eq_left h1]

/-- The vector `s u = (a z, b z, c)`. -/
def tv (lam : ℝ) (z : EuclideanSpace ℝ V) : EuclideanSpace ℝ (Sum V (Sum V (Fin 1))) :=
  WithLp.toLp 2 fun w =>
    match w with
    | Sum.inl v => coefA lam * z v
    | Sum.inr (Sum.inl v) => (1 / 2) * z v
    | Sum.inr (Sum.inr _) => coefC lam

/-- The vector `t u = (a z, -b z, c)`. -/
def tw (lam : ℝ) (z : EuclideanSpace ℝ V) : EuclideanSpace ℝ (Sum V (Sum V (Fin 1))) :=
  WithLp.toLp 2 fun w =>
    match w with
    | Sum.inl v => coefA lam * z v
    | Sum.inr (Sum.inl v) => -(1 / 2) * z v
    | Sum.inr (Sum.inr _) => coefC lam

@[simp] theorem tv_inl (lam : ℝ) (z : EuclideanSpace ℝ V) (v : V) :
    tv lam z (Sum.inl v) = coefA lam * z v := rfl

@[simp] theorem tv_mid (lam : ℝ) (z : EuclideanSpace ℝ V) (v : V) :
    tv lam z (Sum.inr (Sum.inl v)) = (1 / 2) * z v := rfl

@[simp] theorem tv_last (lam : ℝ) (z : EuclideanSpace ℝ V) (i : Fin 1) :
    tv lam z (Sum.inr (Sum.inr i)) = coefC lam := rfl

@[simp] theorem tw_inl (lam : ℝ) (z : EuclideanSpace ℝ V) (v : V) :
    tw lam z (Sum.inl v) = coefA lam * z v := rfl

@[simp] theorem tw_mid (lam : ℝ) (z : EuclideanSpace ℝ V) (v : V) :
    tw lam z (Sum.inr (Sum.inl v)) = -(1 / 2) * z v := rfl

@[simp] theorem tw_last (lam : ℝ) (z : EuclideanSpace ℝ V) (i : Fin 1) :
    tw lam z (Sum.inr (Sum.inr i)) = coefC lam := rfl

/-- The inner product in the three-block space, split into the three blocks. -/
theorem inner_three (P Q : EuclideanSpace ℝ (Sum V (Sum V (Fin 1)))) :
    inner ℝ P Q =
      (∑ v, Q (Sum.inl v) * P (Sum.inl v)) +
        (∑ v, Q (Sum.inr (Sum.inl v)) * P (Sum.inr (Sum.inl v))) +
        Q (Sum.inr (Sum.inr 0)) * P (Sum.inr (Sum.inr 0)) := by
  rw [inner_eucl_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_one]
  abel

theorem inner_tv_tv (lam : ℝ) (z z' : EuclideanSpace ℝ V) :
    inner ℝ (tv lam z) (tv lam z') =
      (coefA lam ^ 2 + 1 / 4) * inner ℝ z z' + coefC lam ^ 2 := by
  rw [inner_three]
  simp only [tv_inl, tv_mid, tv_last]
  have h1 : (∑ v, (coefA lam * z' v) * (coefA lam * z v)) = coefA lam ^ 2 * inner ℝ z z' := by
    rw [inner_eucl_sum z z', Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : (∑ v, ((1 / 2) * z' v) * ((1 / 2) * z v)) = (1 / 4) * inner ℝ z z' := by
    rw [inner_eucl_sum z z', Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2]
  ring

theorem inner_tv_tw (lam : ℝ) (z z' : EuclideanSpace ℝ V) :
    inner ℝ (tv lam z) (tw lam z') =
      (coefA lam ^ 2 - 1 / 4) * inner ℝ z z' + coefC lam ^ 2 := by
  rw [inner_three]
  simp only [tv_inl, tv_mid, tv_last, tw_inl, tw_mid, tw_last]
  have h1 : (∑ v, (coefA lam * z' v) * (coefA lam * z v)) = coefA lam ^ 2 * inner ℝ z z' := by
    rw [inner_eucl_sum z z', Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : (∑ v, (-(1 / 2) * z' v) * ((1 / 2) * z v)) = (-(1 / 4)) * inner ℝ z z' := by
    rw [inner_eucl_sum z z', Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2]
  ring

theorem inner_tw_tw (lam : ℝ) (z z' : EuclideanSpace ℝ V) :
    inner ℝ (tw lam z) (tw lam z') =
      (coefA lam ^ 2 + 1 / 4) * inner ℝ z z' + coefC lam ^ 2 := by
  rw [inner_three]
  simp only [tw_inl, tw_mid, tw_last]
  have h1 : (∑ v, (coefA lam * z' v) * (coefA lam * z v)) = coefA lam ^ 2 * inner ℝ z z' := by
    rw [inner_eucl_sum z z', Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : (∑ v, (-(1 / 2) * z' v) * (-(1 / 2) * z v)) = (1 / 4) * inner ℝ z z' := by
    rw [inner_eucl_sum z z', Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2]
  ring

/-- **Step (ii) of Lemma 4.1**: from an optimal solution of the theta program we get the
vectors `s`, `t` used in the paper. -/
theorem exists_theta_vectors (G : SimpleGraph V) (hϑ : 2 ≤ thetaComplement G)
    (hZ : ∃ Z : Matrix V V ℝ, Z.PosSemidef ∧ (∀ u, Z u u = thetaComplement G - 1) ∧
      ∀ u v, G.Adj u v → Z u v = -1) :
    ∃ s t : V → EuclideanSpace ℝ (Sum V (Sum V (Fin 1))),
      (∀ u, inner ℝ (s u) (s u) = (thetaComplement G - 1) / 2) ∧
      (∀ u, inner ℝ (t u) (t u) = (thetaComplement G - 1) / 2) ∧
      (∀ u, inner ℝ (s u) (t u) = 0) ∧
      (∀ u v, G.Adj u v → inner ℝ (s u) (s v) = 0) ∧
      (∀ u v, G.Adj u v → inner ℝ (t u) (t v) = 0) ∧
      (∀ u v, G.Adj u v → inner ℝ (s u) (t v) = 1 / 2) ∧
      (∀ u v, G.Adj u v → inner ℝ (t u) (s v) = 1 / 2) := by
  classical
  obtain ⟨Z, hZpsd, hZdiag, hZedge⟩ := hZ
  obtain ⟨z, hzgram⟩ := posSemidef_exists_gram hZpsd
  set lam : ℝ := thetaComplement G - 1 with hlam
  have hlam1 : 1 ≤ lam := by rw [hlam]; linarith
  have hA : coefA lam ^ 2 = (lam - 1) / (4 * (lam + 1)) := coefA_sq hlam1
  have hC : coefC lam ^ 2 = lam / (2 * (lam + 1)) := coefC_sq hlam1
  have hden : lam + 1 ≠ 0 := by linarith
  refine ⟨fun u => tv lam (z u), fun u => tw lam (z u), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [inner_tv_tv, hzgram, hZdiag u, hA, hC]
    field_simp
    ring
  · intro u
    rw [inner_tw_tw, hzgram, hZdiag u, hA, hC]
    field_simp
    ring
  · intro u
    rw [inner_tv_tw, hzgram, hZdiag u, hA, hC]
    field_simp
    ring
  · intro u v huv
    rw [inner_tv_tv, hzgram, hZedge u v huv, hA, hC]
    field_simp
    ring
  · intro u v huv
    rw [inner_tw_tw, hzgram, hZedge u v huv, hA, hC]
    field_simp
    ring
  · intro u v huv
    rw [inner_tv_tw, hzgram, hZedge u v huv, hA, hC]
    field_simp
    ring
  · intro u v huv
    rw [real_inner_comm (tv lam (z v)) (tw lam (z u))]
    rw [inner_tv_tw, hzgram, hZedge v u huv.symm, hA, hC]
    field_simp
    ring

end Grothendieck

/-!
# Reduction of Lemma 4.1 to the two analytic facts of the paper

We prove Lemma 4.1 of Briët–de Oliveira Filho–Vallentin under the two inputs that the
paper supplies separately and that are *not* formalised here:

* `hser` (Proposition 4.2, p. 92): for `|t| ≤ 1` the Taylor series of `E_r⁻¹` converges at
  `t β(r,G)` and sums to `E_r⁻¹(t β(r,G))`;
* `habs`, `hval`: absolute convergence of the same series at `β(r,G)`, with
  `∑ k, |b_{2k+1}| β(r,G)^{2k+1} = 1/(ϑ(G)-1)` (equation (4.2));
* `hβle`: `β(r,G) ≤ E_r(1)` (part of Theorem 3.1/Proposition 4.2: `β(r,G)` lies inside the
  radius of convergence);

together with the vectors `s`, `t` produced from an optimal solution of the theta program
(step (ii) of the proof, p. 94).
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Real
open MatrixOrder

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `k`-th block of the Hilbert sum: two copies of
`R^V ⊗ (R^V)^{⊗(2k+1)}`, for the positive and the negative part of the series. -/
abbrev Fib (k : ℕ) : Type _ :=
  EuclideanSpace ℝ (Sum ((Sum V (Sum V (Fin 1))) × (Fin (2 * k + 1) → V)) ((Sum V (Sum V (Fin 1))) × (Fin (2 * k + 1) → V)))

/-- The `k`-th block of the signed feature vector of the pair `(U, W)` at `x`. -/
def featV (r : ℕ) (β : ℝ) (U W : EuclideanSpace ℝ (Sum V (Sum V (Fin 1)))) (x : EuclideanSpace ℝ V)
    (k : ℕ) : Fib (V := V) k :=
  WithLp.toLp 2 fun w =>
    match w with
    | Sum.inl (v, φ) => aCoef r β k * U v * ∏ i : Fin (2 * k + 1), x (φ i)
    | Sum.inr (v, φ) => cCoef r β k * W v * ∏ i : Fin (2 * k + 1), x (φ i)

@[simp]
theorem featV_inl (r : ℕ) (β : ℝ) (U W : EuclideanSpace ℝ (Sum V (Sum V (Fin 1))))
    (x : EuclideanSpace ℝ V) (k : ℕ) (v : Sum V (Sum V (Fin 1))) (φ : Fin (2 * k + 1) → V) :
    featV r β U W x k (Sum.inl (v, φ)) =
      aCoef r β k * U v * ∏ i : Fin (2 * k + 1), x (φ i) := rfl

@[simp]
theorem featV_inr (r : ℕ) (β : ℝ) (U W : EuclideanSpace ℝ (Sum V (Sum V (Fin 1))))
    (x : EuclideanSpace ℝ V) (k : ℕ) (v : Sum V (Sum V (Fin 1))) (φ : Fin (2 * k + 1) → V) :
    featV r β U W x k (Sum.inr (v, φ)) =
      cCoef r β k * W v * ∏ i : Fin (2 * k + 1), x (φ i) := rfl

theorem real_inner_swap (a b : ℝ) : inner ℝ a b = b * a := by simp

theorem sum_mul_eq_inner (U U' : EuclideanSpace ℝ (Sum V (Sum V (Fin 1)))) :
    (∑ v, U v * U' v) = inner ℝ U U' := by
  rw [inner_eq_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The inner product of two signed feature vectors. -/
theorem inner_featV {r : ℕ} (β : ℝ) (k : ℕ)
    (U W U' W' : EuclideanSpace ℝ (Sum V (Sum V (Fin 1)))) (x y : EuclideanSpace ℝ V) :
    inner ℝ (featV r β U W x k) (featV r β U' W' y k) =
      aCoef r β k ^ 2 * inner ℝ U U' * (inner ℝ x y) ^ (2 * k + 1) +
        cCoef r β k ^ 2 * inner ℝ W W' * (inner ℝ x y) ^ (2 * k + 1) := by
  rw [inner_eq_sum (featV r β U W x k) (featV r β U' W' y k), Fintype.sum_sum_type]
  simp only [featV_inl, featV_inr, Fintype.sum_prod_type]
  have key : ∀ (c : ℝ) (A B : (Sum V (Sum V (Fin 1))) → ℝ),
      (∑ v, ∑ φ : Fin (2 * k + 1) → V,
          (c * B v * ∏ i : Fin (2 * k + 1), y (φ i)) *
            (c * A v * ∏ i : Fin (2 * k + 1), x (φ i)))
        = c ^ 2 * (∑ v, A v * B v) * (inner ℝ x y) ^ (2 * k + 1) := by
    intro c A B
    have hU : (∑ v, (c * B v) * (c * A v)) = c ^ 2 * (∑ v, A v * B v) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    have hP : (∑ φ : Fin (2 * k + 1) → V,
        (∏ i : Fin (2 * k + 1), y (φ i)) * (∏ i : Fin (2 * k + 1), x (φ i)))
        = (inner ℝ x y) ^ (2 * k + 1) := by
      rw [← inner_tensPow (2 * k + 1) x y, inner_eq_sum]
      exact Finset.sum_congr rfl fun φ _ => by rw [tensPow_apply, tensPow_apply]
    calc (∑ v, ∑ φ : Fin (2 * k + 1) → V,
            (c * B v * ∏ i : Fin (2 * k + 1), y (φ i)) *
              (c * A v * ∏ i : Fin (2 * k + 1), x (φ i)))
        = ∑ v, ∑ φ : Fin (2 * k + 1) → V,
            ((c * B v) * (c * A v)) *
              ((∏ i : Fin (2 * k + 1), y (φ i)) * (∏ i : Fin (2 * k + 1), x (φ i))) := by
          exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun φ _ => by ring
      _ = (∑ v, (c * B v) * (c * A v)) *
            (∑ φ : Fin (2 * k + 1) → V,
              (∏ i : Fin (2 * k + 1), y (φ i)) * (∏ i : Fin (2 * k + 1), x (φ i))) := by
          rw [Fintype.sum_mul_sum]
      _ = c ^ 2 * (∑ v, A v * B v) * (inner ℝ x y) ^ (2 * k + 1) := by rw [hU, hP]
  rw [key (aCoef r β k) (fun v => U v) (fun v => U' v),
    key (cCoef r β k) (fun v => W v) (fun v => W' v),
    sum_mul_eq_inner U U', sum_mul_eq_inner W W']

end Grothendieck

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 4.1** reduced to the analytic facts about `β(r,G)` and to the theta-program
vectors `s`, `t` (step (ii) of the proof in the paper). -/
theorem vector_construction_reduction
    (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v)
    (f : V → EuclideanSpace ℝ V) (hf : ∀ v, ‖f v‖ = 1)
    (hϑ : 2 ≤ thetaComplement G)
    (hser : ∀ t : ℝ, |t| ≤ 1 →
      Summable (fun k : ℕ => invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) ∧
        (∑' k : ℕ, invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) =
          ErInv r (t * beta r G))
    (habs : Summable (fun k : ℕ => |invCoeff r (2 * k + 1)| * (beta r G) ^ (2 * k + 1)))
    (hneβ : ∃ t : ℝ, 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t)
    (hsumβ : ∀ t : ℝ, beta r G < t →
      Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1))
    (hβR : |beta r G| ≤ Er r 1)
    (s tv : V → EuclideanSpace ℝ (Sum V (Sum V (Fin 1))))
    (hs : ∀ u, inner ℝ (s u) (s u) = (thetaComplement G - 1) / 2)
    (ht : ∀ u, inner ℝ (tv u) (tv u) = (thetaComplement G - 1) / 2)
    (hst : ∀ u, inner ℝ (s u) (tv u) = 0)
    (hse : ∀ u v, G.Adj u v → inner ℝ (s u) (s v) = 0)
    (hte : ∀ u v, G.Adj u v → inner ℝ (tv u) (tv v) = 0)
    (hste : ∀ u v, G.Adj u v → inner ℝ (s u) (tv v) = 1 / 2)
    (htse : ∀ u v, G.Adj u v → inner ℝ (tv u) (s v) = 1 / 2) :
    ∃ g : V → EuclideanSpace ℝ V, (∀ v, ‖g v‖ = 1) ∧
      ∀ u v, G.Adj u v → Er r (inner ℝ (g u) (g v)) = beta r G * inner ℝ (f u) (f v) := by
  classical
  have hval : (∑' k : ℕ, |invCoeff r (2 * k + 1)| * (beta r G) ^ (2 * k + 1)) =
      (thetaComplement G - 1)⁻¹ := by
    have h := betaSeries_beta_eq r G hϑ hneβ hsumβ
    rw [betaSeries] at h
    rw [h, one_div]
  set β := beta r G with hβdef
  set lam := thetaComplement G - 1 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; linarith
  have hβnn : 0 ≤ β := by
    rw [hβdef]
    exact Real.sInf_nonneg fun x hx => hx.1
  have hval' : (∑' k : ℕ, |invCoeff r (2 * k + 1)| * β ^ (2 * k + 1)) = lam⁻¹ := by
    rw [hβdef, hlamdef]
    exact hval
  -- the diagonal inner products of the `s`/`t` blocks
  have hsym : ∀ u v : V, inner ℝ (tv u) (s v) = inner ℝ (s v) (tv u) :=
    fun u v => (real_inner_comm (tv u) (s v)).symm
  have hU : ∀ u : V, inner ℝ (s u + tv u) (s u + tv u) = lam := by
    intro u
    have h0 : inner ℝ (tv u) (s u) = 0 := by rw [hsym u u, hst u]
    rw [inner_add_left, inner_add_right, inner_add_right, hs u, ht u, hst u, h0]
    ring
  have hW : ∀ u : V, inner ℝ (s u - tv u) (s u - tv u) = lam := by
    intro u
    have h0 : inner ℝ (tv u) (s u) = 0 := by rw [hsym u u, hst u]
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hs u, ht u, hst u, h0]
    ring
  -- norms of the blocks
  have hnorm : ∀ (u : V) (k : ℕ),
      inner ℝ (featV r β (s u + tv u) (s u - tv u) (f u) k)
          (featV r β (s u + tv u) (s u - tv u) (f u) k)
        = lam * (|invCoeff r (2 * k + 1)| * β ^ (2 * k + 1)) := by
    intro u k
    rw [inner_featV, hU u, hW u, real_inner_self_eq_norm_sq (f u), hf u]
    simp only [one_pow, mul_one]
    rw [← add_mul, aCoef_sq_add_cCoef_sq (r := r) hβnn]
    ring
  have hmem : ∀ u : V, Memℓp (fun k : ℕ => featV r β (s u + tv u) (s u - tv u) (f u) k) 2 := by
    intro u
    refine memℓp_gen ?_
    have h2 : ∀ k : ℕ,
        ‖featV r β (s u + tv u) (s u - tv u) (f u) k‖ ^ (2 : ℝ)
          = lam * (|invCoeff r (2 * k + 1)| * β ^ (2 * k + 1)) := by
      intro k
      rw [Real.rpow_two, ← real_inner_self_eq_norm_sq]
      exact hnorm u k
    exact (habs.mul_left lam).congr fun k => (h2 k).symm
  -- the vectors `R u` of the Hilbert sum
  set R : V → lp (Fib (V := V)) 2 := fun u =>
    ⟨fun k => featV r β (s u + tv u) (s u - tv u) (f u) k, hmem u⟩ with hR
  -- their Gram matrix
  set M : Matrix V V ℝ := Matrix.gram ℝ R with hM
  have hMpsd : M.PosSemidef := Matrix.posSemidef_gram ℝ R
  have hterm : ∀ (u v : V), G.Adj u v → ∀ k : ℕ,
      inner ℝ (R u k) (R v k) =
        invCoeff r (2 * k + 1) * (inner ℝ (f u) (f v) * β) ^ (2 * k + 1) := by
    intro u v huv k
    have h3 : inner ℝ (tv u) (s v) = 1 / 2 := htse u v huv
    have h1 : inner ℝ (s u + tv u) (s v + tv v) = 1 := by
      rw [inner_add_left, inner_add_right, inner_add_right, hse u v huv, hte u v huv,
        hste u v huv, h3]
      norm_num
    have h2 : inner ℝ (s u - tv u) (s v - tv v) = -1 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, hse u v huv, hte u v huv,
        hste u v huv, h3]
      norm_num
    rw [inner_featV, h1, h2]
    simp only [mul_one]
    have h4 : aCoef r β k ^ 2 * inner ℝ (f u) (f v) ^ (2 * k + 1) +
        cCoef r β k ^ 2 * (-1) * inner ℝ (f u) (f v) ^ (2 * k + 1) =
        (aCoef r β k ^ 2 - cCoef r β k ^ 2) * inner ℝ (f u) (f v) ^ (2 * k + 1) := by
      ring
    rw [h4, aCoef_sq_sub_cCoef_sq (r := r) hβnn]
    ring
  -- diagonal entries
  have hdiagM : ∀ u : V, M u u = 1 := by
    intro u
    simp only [hM, Matrix.gram_apply]
    rw [lp.inner_eq_tsum]
    have hstep : ∀ k : ℕ, inner ℝ (R u k) (R u k) = lam * (|invCoeff r (2 * k + 1)| * β ^ (2 * k + 1)) :=
      fun k => hnorm u k
    rw [tsum_congr hstep, tsum_mul_left, hval']
    exact mul_inv_cancel₀ (ne_of_gt hlampos)
  -- edge entries
  have hedge : ∀ u v : V, G.Adj u v → M u v = ErInv r (β * inner ℝ (f u) (f v)) := by
    intro u v huv
    simp only [hM, Matrix.gram_apply]
    rw [lp.inner_eq_tsum]
    have ht0 : |inner ℝ (f u) (f v)| ≤ 1 := by
      have := abs_real_inner_le_norm (f u) (f v)
      rwa [hf u, hf v, one_mul] at this
    rw [tsum_congr fun k => hterm u v huv k]
    have := (hser (inner ℝ (f u) (f v)) ht0).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- Cholesky: realise the Gram matrix in `R^V`
  have hnonneg : (0 : Matrix V V ℝ) ≤ M := hMpsd.nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnonneg
  have hgram : ∀ u v : V,
      inner ℝ (WithLp.toLp 2 fun w => B w u) (WithLp.toLp 2 fun w => B w v) = M u v := by
    intro u v
    rw [PiLp.inner_apply]
    have hMuv : M u v = (star B * B) u v := by rw [hB]
    rw [hMuv, Matrix.mul_apply]
    simp only [Matrix.star_apply, star_trivial, real_inner_swap]
    exact Finset.sum_congr rfl fun w _ => by ring
  refine ⟨fun u => WithLp.toLp 2 (fun w => B w u), ?_, ?_⟩
  · intro u
    have h1 : inner ℝ (WithLp.toLp 2 fun w => B w u) (WithLp.toLp 2 fun w => B w u) = 1 := by
      rw [hgram, hdiagM]
    have h2 : ‖WithLp.toLp 2 (fun w => B w u)‖ = 1 := by
      have h3 : ‖WithLp.toLp 2 (fun w => B w u)‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq (WithLp.toLp 2 fun w => B w u), h1]
      nlinarith [norm_nonneg (WithLp.toLp 2 fun w => B w u)]
    exact h2
  · intro u v huv
    have h1 : inner ℝ (WithLp.toLp 2 fun w => B w u) (WithLp.toLp 2 fun w => B w v)
        = ErInv r (β * inner ℝ (f u) (f v)) := by
      rw [hgram, hedge u v huv]
    rw [h1, Er_ErInv_of_abs_le hr, mul_comm]
    -- `|β * inner (f u) (f v)| ≤ E_r(1)`
    rw [abs_mul]
    have ht0 : |inner ℝ (f u) (f v)| ≤ 1 := by
      have := abs_real_inner_le_norm (f u) (f v)
      rwa [hf u, hf v, one_mul] at this
    calc |β| * |inner ℝ (f u) (f v)| ≤ |β| * 1 := by
          exact mul_le_mul_of_nonneg_left ht0 (abs_nonneg β)
      _ = |β| := mul_one _
      _ ≤ Er r 1 := hβR

/-- **Lemma 4.1**, with step (ii) of the paper's proof (the theta program) supplied by an
optimal solution `Z` of the semidefinite program (4.1). -/
theorem vector_construction_of_theta_proof (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V)
    (hne : ∃ u v, G.Adj u v) (f : V → EuclideanSpace ℝ V) (hf : ∀ v, ‖f v‖ = 1)
    (hϑ : 2 ≤ thetaComplement G)
    (hser : ∀ t : ℝ, |t| ≤ 1 →
      Summable (fun k : ℕ => invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) ∧
        (∑' k : ℕ, invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) =
          ErInv r (t * beta r G))
    (habs : Summable (fun k : ℕ => |invCoeff r (2 * k + 1)| * (beta r G) ^ (2 * k + 1)))
    (hneβ : ∃ t : ℝ, 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t)
    (hsumβ : ∀ t : ℝ, beta r G < t →
      Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1))
    (hβR : |beta r G| ≤ Er r 1)
    (hZ : ∃ Z : Matrix V V ℝ, Z.PosSemidef ∧ (∀ u, Z u u = thetaComplement G - 1) ∧
      ∀ u v, G.Adj u v → Z u v = -1) :
    ∃ g : V → EuclideanSpace ℝ V, (∀ v, ‖g v‖ = 1) ∧
      ∀ u v, G.Adj u v → Er r (inner ℝ (g u) (g v)) = beta r G * inner ℝ (f u) (f v) := by
  obtain ⟨s, t, h1, h2, h3, h4, h5, h6, h7⟩ := exists_theta_vectors G hϑ hZ
  exact vector_construction_reduction r hr G hne f hf hϑ hser habs hneβ hsumβ hβR s t
    h1 h2 h3 h4 h5 h6 h7

end Grothendieck

open Grothendieck in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V)
    (hne : ∃ u v, G.Adj u v) (f : V → EuclideanSpace ℝ V) (hf : ∀ v, ‖f v‖ = 1)
    (hϑ : 2 ≤ thetaComplement G)
    (hser : ∀ t : ℝ, |t| ≤ 1 →
      Summable (fun k : ℕ => invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) ∧
        (∑' k : ℕ, invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) =
          ErInv r (t * beta r G))
    (habs : Summable (fun k : ℕ => |invCoeff r (2 * k + 1)| * (beta r G) ^ (2 * k + 1)))
    (hneβ : ∃ t : ℝ, 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t)
    (hsumβ : ∀ t : ℝ, beta r G < t →
      Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1))
    (hβR : |beta r G| ≤ Er r 1)
    (hZ : ∃ Z : Matrix V V ℝ, Z.PosSemidef ∧ (∀ u, Z u u = thetaComplement G - 1) ∧
      ∀ u v, G.Adj u v → Z u v = -1) :
    ∃ g : V → EuclideanSpace ℝ V, (∀ v, ‖g v‖ = 1) ∧
      ∀ u v, G.Adj u v → Er r (inner ℝ (g u) (g v)) = beta r G * inner ℝ (f u) (f v) :=
  vector_construction_of_theta_proof r hr G hne f hf hϑ hser habs hneβ hsumβ hβR hZ
