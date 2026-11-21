-- Prove2me | solution 1 for MasulloRH.prime_orbit_overlap_relative_euler_scale
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:18:16.273216+00:00
-- url     : https://prove2.me/submissions/2101e0ea-ffb3-4e5b-b0ac-b26dd98cf357

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Filter Finset
open scoped Topology

private lemma product_bound (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    1 + ∑ n ∈ s, f n ≤ ∏ n ∈ s, (1+f n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, Finset.prod_insert hn]
    have h := mul_le_mul_of_nonneg_left ih (by linarith [hf n] : 0 ≤ 1 + f n)
    have hp := mul_nonneg (hf n) (Finset.sum_nonneg (fun i (_ : i ∈ s) => hf i))
    linarith

theorem solution (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1) :
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let r (p : ℕ) := (p : ℝ)^(-a)
    let C (B : ℕ) := ∏ p ∈ P B, (1-r p)/(1+r p)
    let E (B : ℕ) := ∏ p ∈ P B, (1-r p)
    (∀ B, 0 < E B ∧ C B / E B = (∏ p ∈ P B, (1+r p))⁻¹) ∧
    Tendsto (fun B => C B / E B) atTop (𝓝 0) := by
  dsimp only
  let f (n : ℕ) : ℝ := if n.Prime then (n:ℝ)^(-a) else 0
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hns : ¬ Summable f := by
    intro h
    have hbad := Nat.Primes.summable_rpow.mp ((Nat.Primes.summable_iff_summable_ite (fun n : ℕ ↦ (n:ℝ)^(-a))).mpr h)
    linarith
  have htop := ((not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp hns).comp (tendsto_add_atTop_nat 1)
  have hprod (B : ℕ) : ∏ p ∈ (range (B+1)).filter Nat.Prime, (1+(p:ℝ)^(-a)) =
      ∏ n ∈ range (B+1), (1+f n) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro n _
    by_cases h : n.Prime <;> simp [f,h]
  have he (B : ℕ) : 0 < ∏ p ∈ (range (B+1)).filter Nat.Prime, (1-(p:ℝ)^(-a)) := by
    apply Finset.prod_pos
    intro p hp
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt) (by linarith))
  have hid (B : ℕ) : (∏ p ∈ (range (B+1)).filter Nat.Prime, (1-(p:ℝ)^(-a))/(1+(p:ℝ)^(-a))) /
      (∏ p ∈ (range (B+1)).filter Nat.Prime, (1-(p:ℝ)^(-a))) =
      (∏ p ∈ (range (B+1)).filter Nat.Prime, (1+(p:ℝ)^(-a)))⁻¹ := by
    rw [Finset.prod_div_distrib, div_right_comm, div_self (he B).ne', one_div]
  refine ⟨fun B => ⟨he B, hid B⟩, ?_⟩
  simp_rw [hid, hprod]
  apply Filter.Tendsto.inv_tendsto_atTop
  apply tendsto_atTop_mono (fun B => le_trans (by linarith : (∑ n ∈ range (B+1), f n) ≤ 1+ ∑ n ∈ range (B+1), f n) (product_bound _ f hf))
  exact htop
