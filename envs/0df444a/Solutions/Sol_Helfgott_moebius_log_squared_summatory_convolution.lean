-- Prove2me | solution 1 for Helfgott.moebius_log_squared_summatory_convolution
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T19:47:36.474992+00:00
-- url     : https://prove2.me/submissions/aaaffeda-67e0-4241-85fb-1525e3fcaae5

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def logWeightAF (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log (n : ℝ), by simp⟩

@[simp] lemma logWeightAF_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logWeightAF f n = f n * Real.log (n : ℝ) := rfl

lemma logWeightAF_neg (f : ArithmeticFunction ℝ) :
    logWeightAF (-f) = -logWeightAF f := by
  ext n
  simp only [logWeightAF_apply, ArithmeticFunction.neg_apply, neg_mul]

lemma logWeightAF_mul (f g : ArithmeticFunction ℝ) :
    logWeightAF (f * g) = logWeightAF f * g + f * logWeightAF g := by
  ext n
  simp only [logWeightAF_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  have he : (p.1 : ℝ) * (p.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← he, Real.log_mul (Nat.cast_ne_zero.mpr hp0.1) (Nat.cast_ne_zero.mpr hp0.2)]
  ring

lemma logWeightAF_moebius :
    logWeightAF (moebius : ArithmeticFunction ℝ) =
      -((moebius : ArithmeticFunction ℝ) * vonMangoldt) := by
  have hz : logWeightAF (moebius : ArithmeticFunction ℝ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = -vonMangoldt := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    simp only [logWeightAF_apply, ArithmeticFunction.intCoe_apply, ArithmeticFunction.neg_apply]
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  have h := congrArg (fun f : ArithmeticFunction ℝ => f * (moebius : ArithmeticFunction ℝ)) hz
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at h
  calc
    _ = -vonMangoldt * (moebius : ArithmeticFunction ℝ) := h
    _ = -((moebius : ArithmeticFunction ℝ) * vonMangoldt) := by ring

lemma logWeightAF_moebius_squared :
    logWeightAF (logWeightAF (moebius : ArithmeticFunction ℝ)) =
      (moebius : ArithmeticFunction ℝ) *
        (vonMangoldt * vonMangoldt - logWeightAF vonMangoldt) := by
  rw [logWeightAF_moebius, logWeightAF_neg, logWeightAF_mul, logWeightAF_moebius]
  ring

theorem moebius_log_squared_pointwise_convolution (n : ℕ) :
    ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2 =
      ∑ p ∈ n.divisorsAntidiagonal, ((moebius p.1 : ℤ) : ℝ) *
        ((vonMangoldt * vonMangoldt) p.2 - vonMangoldt p.2 * Real.log (p.2 : ℝ)) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) logWeightAF_moebius_squared
  rw [logWeightAF_apply, logWeightAF_apply, ArithmeticFunction.mul_apply] at h
  simp only [ArithmeticFunction.intCoe_apply, sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, logWeightAF_apply] at h
  simp only [← sub_eq_add_neg] at h
  calc
    _ = ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
    _ = _ := h

theorem moebius_log_squared_summatory_convolution_complete (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) *
        ∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)) := by
  have hpoint (n : ℕ) :
      ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2 =
        ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) *
          ((vonMangoldt * vonMangoldt) (n / d) -
            vonMangoldt (n / d) * Real.log (n / d : ℕ)) := by
    rw [moebius_log_squared_pointwise_convolution]
    exact Nat.sum_divisorsAntidiagonal (fun d k : ℕ => ((moebius d : ℤ) : ℝ) *
      ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)))
  simp_rw [hpoint]
  rw [finite_positive_divisor_reindex ⌊x⌋₊ (fun d k : ℕ => ((moebius d : ℤ) : ℝ) *
    ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)))]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast, Finset.mul_sum]

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution  (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) *
        ∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)) := Helfgott.moebius_log_squared_summatory_convolution_complete x

#print axioms solution
