-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.product_pow_coeff_ne_zero_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:23:30.120982+00:00
-- url     : https://prove2.me/submissions/98bc8b7f-33bc-403b-90d6-1480722385e2

import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (T d : σ → ℕ) (k : ℕ)
    (hτs : ∀ i n, n < T i → PowerSeries.coeff n (τ i) = 0)
    (hne : PowerSeries.coeff k (∏ i, τ i ^ d i) ≠ 0) :
    ∑ i, T i * d i ≤ k := by
  have hbase (i : σ) : (T i : ℕ∞) ≤ (τ i).order :=
    PowerSeries.nat_le_order (τ i) (T i) (hτs i)
  have hpow (i : σ) : ((T i * d i : ℕ) : ℕ∞) ≤ (τ i ^ d i).order := by
    calc
      _ = d i • (T i : ℕ∞) := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ d i • (τ i).order := nsmul_le_nsmul_right (hbase i) _
      _ ≤ _ := PowerSeries.le_order_pow (τ i) (d i)
  have hprod : ((∑ i, T i * d i : ℕ) : ℕ∞) ≤ (∏ i, τ i ^ d i).order := by
    calc
      _ = ∑ i, ((T i * d i : ℕ) : ℕ∞) := by simp
      _ ≤ ∑ i, (τ i ^ d i).order := Finset.sum_le_sum (fun i _ => hpow i)
      _ ≤ _ := PowerSeries.le_order_prod (fun i => τ i ^ d i) Finset.univ
  have hbound := hprod.trans (PowerSeries.order_le k hne)
  exact_mod_cast hbound

#print axioms solution
