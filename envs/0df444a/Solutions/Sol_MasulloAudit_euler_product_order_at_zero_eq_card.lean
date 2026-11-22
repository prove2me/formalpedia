-- Prove2me | solution 1 for MasulloAudit.euler_product_order_at_zero_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:05:50.33606+00:00
-- url     : https://prove2.me/submissions/aea2b326-57dd-4dba-a7c7-0659950c17e4

import Mathlib

open Complex

/-- Each Euler factor `s ↦ 1 - p^{-s}` is analytic at every point. -/
lemma euler_factor_analyticAt (p : Nat.Primes) (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => 1 - ((p : ℕ) : ℂ) ^ (-s)) z := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hslit : (((p : ℕ) : ℂ)) ∈ slitPlane := by
    rw [show (((p : ℕ) : ℂ)) = (((p : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    exact ofReal_mem_slitPlane.mpr hp
  exact analyticAt_const.sub (analyticAt_const.cpow analyticAt_id.neg hslit)

/-- Each Euler factor vanishes to order exactly one at `s = 0`. -/
lemma euler_factor_order (p : Nat.Primes) :
    analyticOrderAt (fun s : ℂ => 1 - ((p : ℕ) : ℂ) ^ (-s)) 0 = 1 := by
  have hp0 : (((p : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hd : HasDerivAt (fun s : ℂ => 1 - ((p : ℕ) : ℂ) ^ (-s))
      (-(((p : ℕ) : ℂ) ^ (-(0 : ℂ)) * Complex.log ((p : ℕ)) * (-1))) 0 :=
    ((hasDerivAt_id (0 : ℂ)).neg.const_cpow (Or.inl hp0)).const_sub 1
  apply (euler_factor_analyticAt p 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp
  · rw [hd.deriv]
    have hlog : Complex.log ((p : ℕ) : ℂ) ≠ 0 := by
      rw [show (((p : ℕ) : ℂ)) = (((p : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_log (by positivity)]
      exact_mod_cast (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
    simpa using hlog

/-- The finite Euler product `∏_{p ∈ S} (1 - p^{-s})` vanishes to order exactly `|S|` at `0`. -/
theorem solution (S : Finset Nat.Primes) :
    analyticOrderAt (fun s : ℂ => ∏ p ∈ S, (1 - ((p : ℕ) : ℂ) ^ (-s))) 0 = S.card := by
  classical
  induction S using Finset.induction with
  | empty => simp [analyticOrderAt_eq_zero]
  | insert a S ha ih =>
    have hprod : AnalyticAt ℂ (fun s : ℂ => ∏ p ∈ S, (1 - ((p : ℕ) : ℂ) ^ (-s))) 0 :=
      Finset.analyticAt_fun_prod S (fun p _ => euler_factor_analyticAt p 0)
    have := analyticOrderAt_mul (euler_factor_analyticAt a 0) hprod
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    rw [show (fun s : ℂ => (1 - ((a : ℕ) : ℂ) ^ (-s)) * ∏ p ∈ S, (1 - ((p : ℕ) : ℂ) ^ (-s))) =
      (fun s : ℂ => 1 - ((a : ℕ) : ℂ) ^ (-s)) * (fun s : ℂ => ∏ p ∈ S, (1 - ((p : ℕ) : ℂ) ^ (-s)))
      from rfl, this, euler_factor_order, ih]
    push_cast; ring


