-- Prove2me | solution 1 for Height.nonarchimedean_monic_root_le_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T23:43:10.447005+00:00
-- url     : https://prove2.me/submissions/08161234-d01a-464b-91b4-4f3fdd3efeeb

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: standalone nonarchimedean monic root bound for public reuse.
Named downstream consumer: local bounds for actual original theta norm chart equations. -/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Polynomial Finset
universe u

theorem solution {K : Type u} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {p : Polynomial K} (hp : p.Monic) {a : K} (ha : p.IsRoot a)
    {B : ℝ} (hB : 1 ≤ B) (hc : ∀ i < p.natDegree, v (p.coeff i) ≤ B) : v a ≤ B := by
  by_contra! hlt
  have hOne : 1 < v a := hB.trans_lt hlt
  have hpos : 0 < v a := zero_lt_one.trans hOne
  have hlead : v (p.coeff p.natDegree * a ^ p.natDegree) = v a ^ p.natDegree := by
    rw [hp.coeff_natDegree, one_mul, map_pow]
  have hdom : ∀ i ∈ range (p.natDegree+1), i ≠ p.natDegree →
      v (p.coeff i * a ^ i) < v (p.coeff p.natDegree * a ^ p.natDegree) := by
    intro i hi hne
    have hi' : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hi)) hne
    rw [hlead, map_mul, map_pow]
    calc
      _ ≤ B * v a ^ i := mul_le_mul_of_nonneg_right (hc i hi') (pow_nonneg (v.nonneg a) _)
      _ < v a * v a ^ i := mul_lt_mul_of_pos_right hlt (pow_pos hpos _)
      _ = v a ^ (i+1) := (pow_succ' _ _).symm
      _ ≤ v a ^ p.natDegree := pow_le_pow_right₀ hOne.le (Nat.succ_le_of_lt hi')
  have hs := hv.apply_sum_eq_of_lt (by intro z; simp) (s := range (p.natDegree+1))
    (l := fun i => p.coeff i * a ^ i) (k := p.natDegree) (by simp) hdom
  have hz : ∑ i ∈ range (p.natDegree+1), p.coeff i * a ^ i = 0 := by
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range] using ha
  rw [hz, map_zero, hlead] at hs
  exact (ne_of_gt (pow_pos hpos _)) hs.symm

#print axioms solution
