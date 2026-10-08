-- Prove2me | solution 1 for IntervalExchange.exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T09:26:03.778974+00:00
-- url     : https://prove2.me/submissions/bad53a1a-7c14-4d09-a7e9-8b7a0cebf66f

import Mathlib
import Definitions.Def_IntervalExchange

namespace IntervalExchange

namespace IETReadingsP2

abbrev G := Multiplicative (ZMod 2)

noncomputable def ν : G →₀ ℝ := Finsupp.single (Multiplicative.ofAdd 1) 1

lemma kernel (x y : G) :
    walkKernel (ν : G → ℝ) x y = if y = Multiplicative.ofAdd 1 * x then 1 else 0 := by
  classical
  unfold walkKernel
  rw [tsum_fintype]
  rw [Finset.sum_eq_single (Multiplicative.ofAdd 1)]
  · simp only [ν, Finsupp.single_eq_same, smul_eq_mul]
    by_cases h : Multiplicative.ofAdd (1 : ZMod 2) * x = y
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro b _ hb
    simp [ν, Ne.symm hb]
  · simp

lemma step (n : ℕ) (y : G) :
    stepProb (walkKernel (ν : G → ℝ)) n 1 y =
      if y = Multiplicative.ofAdd 1 ^ n then 1 else 0 := by
  classical
  induction n generalizing y with
  | zero => simp [stepProb]
  | succ n ih =>
    simp only [stepProb]
    rw [tsum_fintype]
    simp_rw [ih, kernel]
    rw [Finset.sum_eq_single (Multiplicative.ofAdd 1 ^ n)]
    · simp [pow_succ']
    · intro b _ hb; simp [hb]
    · simp

end IETReadingsP2

open IETReadingsP2 in
theorem chk_exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd :
    ∃ ν : Multiplicative (ZMod 2) →₀ ℝ, ThompsonAmenability.IsProbability ν ∧ IsSymmetric ν ∧
      IsNondegenerate ν ∧
      ∀ n : ℕ, Odd n → stepProb (walkKernel (ν : Multiplicative (ZMod 2) → ℝ)) n (1 : Multiplicative (ZMod 2)) 1 = 0 := by
  refine ⟨IETReadingsP2.ν, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g; simp only [IETReadingsP2.ν, Finsupp.single_apply]; split_ifs <;> norm_num
  · simp [IETReadingsP2.ν]
  · intro g
    have : ∀ g : Multiplicative (ZMod 2), g⁻¹ = g := by decide
    rw [this]
  · unfold IsNondegenerate; rw [eq_top_iff]
    intro g _
    have hs : (IETReadingsP2.ν.support : Set (Multiplicative (ZMod 2))) = {Multiplicative.ofAdd 1} := by
      simp [IETReadingsP2.ν]
    rw [hs]
    have : ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = Multiplicative.ofAdd 1 := by decide
    rcases this g with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure rfl
  · intro n hn
    rw [IETReadingsP2.step]
    rcases hn with ⟨k, rfl⟩
    have : (Multiplicative.ofAdd (1 : ZMod 2)) ^ (2 * k + 1) = Multiplicative.ofAdd 1 := by
      rw [pow_succ, pow_mul]
      have : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
      simp [this]
    rw [this, if_neg (by decide)]

end IntervalExchange


open IntervalExchange in
theorem solution :
    ∃ ν : Multiplicative (ZMod 2) →₀ ℝ, ThompsonAmenability.IsProbability ν ∧ IsSymmetric ν ∧
      IsNondegenerate ν ∧
      ∀ n : ℕ, Odd n → stepProb (walkKernel (ν : Multiplicative (ZMod 2) → ℝ)) n (1 : Multiplicative (ZMod 2)) 1 = 0 :=
  IntervalExchange.chk_exists_isSymmetric_isNondegenerate_and_stepProb_eq_zero_of_odd
