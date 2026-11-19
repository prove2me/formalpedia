-- Prove2me | solution 1 for LevyStochCalc.Analysis.le_mul_pow_div_factorial_of_le_mul_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:12:49.225751+00:00
-- url     : https://prove2.me/submissions/1cc4d163-c6f3-46d4-a477-7d5e0f283c5b

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A Grönwall inequality in integral form

A nonnegative function bounded by a multiple of its own running integral is identically zero:
iterating the inequality bounds it by `B·(c(t−a))ᵐ/m!` for every `m`, and that tends to zero.
-/

open MeasureTheory

namespace LevyStochCalc.Analysis



theorem _root_.solution {a b c B : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf0 : ∀ t, 0 ≤ f t)
    (hB : ∀ t ∈ Set.Icc a b, f t ≤ B)
    (hineq : ∀ t ∈ Set.Icc a b, f t ≤ c * ∫ u in Set.Ioc a t, f u) (m : ℕ) :
    ∀ t ∈ Set.Icc a b, f t ≤ B * (c * (t - a)) ^ m / (m).factorial := by
  have hint : ∀ t ∈ Set.Icc a b, IntegrableOn f (Set.Ioc a t) := by
    intro t ht
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (hf.mono_measure (Measure.restrict_mono (show Set.Ioc a t ⊆ Set.Icc a b from fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩) le_rfl)) B ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u)]
    exact hB u ⟨hu.1.le, hu.2.trans ht.2⟩
  induction m with
  | zero =>
    intro t ht
    simpa using hB t ht
  | succ m ih =>
    intro t ht
    have hat : a ≤ t := ht.1
    have hg : Continuous (fun u : ℝ => B * (c * (u - a)) ^ m / (m.factorial : ℝ)) := by fun_prop
    have hgint : IntegrableOn (fun u : ℝ => B * (c * (u - a)) ^ m / (m.factorial : ℝ))
        (Set.Ioc a t) := (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hmono : ∫ u in Set.Ioc a t, f u ≤
        ∫ u in Set.Ioc a t, B * (c * (u - a)) ^ m / (m.factorial : ℝ) :=
      setIntegral_mono_on (hint t ht) hgint measurableSet_Ioc
        (fun u hu => ih u ⟨hu.1.le, hu.2.trans ht.2⟩)
    have hcomp : ∫ u in Set.Ioc a t, B * (c * (u - a)) ^ m / (m.factorial : ℝ) =
        B * c ^ m / (m.factorial : ℝ) * ((t - a) ^ (m + 1) / (m + 1)) := by
      rw [← intervalIntegral.integral_of_le hat]
      have : (fun u : ℝ => B * (c * (u - a)) ^ m / (m.factorial : ℝ)) =
          fun u => B * c ^ m / (m.factorial : ℝ) * (u - a) ^ m := by
        funext u; rw [mul_pow]; ring
      rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
        (fun x => x ^ m), integral_pow]
      simp
    calc f t ≤ c * ∫ u in Set.Ioc a t, f u := hineq t ht
      _ ≤ c * (B * c ^ m / (m.factorial : ℝ) * ((t - a) ^ (m + 1) / (m + 1))) := by
          rw [← hcomp]; exact mul_le_mul_of_nonneg_left hmono hc
      _ = B * (c * (t - a)) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, mul_pow, pow_succ c]
          push_cast
          field_simp

