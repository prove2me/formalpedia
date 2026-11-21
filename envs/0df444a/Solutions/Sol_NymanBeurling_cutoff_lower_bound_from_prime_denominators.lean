-- Prove2me | solution 1 for NymanBeurling.cutoff_lower_bound_from_prime_denominators
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:47:22.173958+00:00
-- url     : https://prove2.me/submissions/a6b4a521-a70b-47eb-9cef-b64e718c9828

import Theorems.Thm_NymanBeurling_prime_coefficient_sq_le_certificate
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset

private theorem cutoff_of_prime_bounds (J H : ℕ) (c : ℕ →₀ ℚ) (P : Finset ℕ) (cost : ℚ)
    (haccuracy : cost < 1 / (J + 1 : ℚ))
    (htail : (1 + ∑ k ∈ c.support, |c k|)^2 / (H+1 : ℚ) ≤ cost)
    (hprime : ∀ k ∈ P, (k+2).Prime)
    (hsize : ∀ k ∈ P, 8*((k : ℚ)+2)^2+24 ≤ (J+1 : ℚ))
    (hcoeff : ∀ k, (k+2).Prime → (1 - c k)^2 ≤ (2*((k : ℚ)+2)^2+6) * cost) :
    (J+1 : ℚ) * (1+(P.card : ℚ)/2)^2 < (H+1 : ℚ) := by
  have hJ : (0:ℚ) < J + 1 := by positivity
  have hH : (0:ℚ) < H + 1 := by positivity
  have hpos (k : ℕ) : (0:ℚ) < 2*((k : ℚ)+2)^2+6 := by positivity
  have hlb (k : ℕ) (hk : k ∈ P) : (1/2 : ℚ) < c k := by
    let v : ℚ := 2*((k : ℚ)+2)^2+6
    have hsmall : v * cost < v / (J + 1 : ℚ) := by
      simpa [div_eq_mul_inv] using mul_lt_mul_of_pos_left haccuracy (hpos k)
    have hv : v / (J + 1 : ℚ) ≤ 1/4 := by
      apply (div_le_iff₀ hJ).mpr
      dsimp [v]
      linarith [hsize k hk]
    have hquad := (hcoeff k (hprime k hk)).trans_lt (hsmall.trans_le hv)
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show (0:ℚ) ≤ 1-c k by linarith)]
  have hsub : P ⊆ c.support := by
    intro k hk
    exact Finsupp.mem_support_iff.mpr (ne_of_gt (lt_trans (by norm_num : (0:ℚ)<1/2) (hlb k hk)))
  have hbudget : (P.card : ℚ)/2 ≤ ∑ k ∈ c.support, |c k| := calc
    (P.card : ℚ)/2 = ∑ k ∈ P, (1/2 : ℚ) := by simp [nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ ∑ k ∈ P, |c k| := sum_le_sum fun k hk ↦ (hlb k hk).le.trans (le_abs_self _)
    _ ≤ ∑ k ∈ c.support, |c k| := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ abs_nonneg _)
  have hl : (0 : ℚ) ≤ 1 + (P.card : ℚ)/2 := by positivity
  have hsq : (1 + (P.card : ℚ)/2)^2 ≤ (1 + ∑ k ∈ c.support, |c k|)^2 :=
    pow_le_pow_left₀ hl (by linarith) _
  have hand := (div_lt_div_iff₀ hH hJ).mp (htail.trans_lt haccuracy)
  simpa only [one_mul,mul_comm] using (mul_le_mul_of_nonneg_right hsq hJ.le).trans_lt hand

theorem solution (c : ℕ →₀ ℚ) (J H : ℕ) (P : Finset ℕ)
    (haccuracy : ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1 / (J + 1 : ℚ))
    (hprime : ∀ k ∈ P, (k+2).Prime)
    (hsize : ∀ k ∈ P, 8*((k : ℚ)+2)^2+24 ≤ (J+1 : ℚ)) :
    (J+1 : ℚ) * (1+(P.card : ℚ)/2)^2 < (H+1 : ℚ) := by
  classical
  let head : ℚ := ∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))
  let tailPart : ℚ := (1 + ∑ k ∈ c.support, |c k|)^2/(H+1 : ℚ)
  have hh : 0 ≤ head := by dsimp [head]; positivity
  have ht : 0 ≤ tailPart := by dsimp [tailPart]; positivity
  apply cutoff_of_prime_bounds J H c P (head + tailPart) haccuracy (by linarith) hprime hsize
  intro k hp
  have hc := NymanBeurling.prime_coefficient_sq_le_certificate c H (k+2) hp
  have hcompare : (if k+2=2 then (14:ℚ) else 2*(((k+2:ℕ):ℚ))^2+2) ≤ 2*((k:ℚ)+2)^2+6 := by
    split_ifs with he
    · have : k = 0 := by omega
      subst k
      norm_num
    · push_cast
      linarith
  have hcc : (1-c k)^2 ≤ (if k+2=2 then (14:ℚ) else 2*(((k+2:ℕ):ℚ))^2+2) * (head+tailPart) := by
    simpa only [Nat.add_sub_cancel] using hc
  exact hcc.trans (mul_le_mul_of_nonneg_right hcompare (add_nonneg hh ht))
