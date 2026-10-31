-- Prove2me | solution 1 for MarkovProcess.perturbed_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:30:36.429228+00:00
-- url     : https://prove2.me/submissions/0e2b0fa1-07a1-498b-83f9-49f9752a827c

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

namespace MarkovProcess

noncomputable section

private theorem function_eq_zero_of_geometric_bound {alpha : Type*} {d : alpha → ℝ}
    {r D : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hD0 : 0 ≤ D)
    (himprove : ∀ {B : ℝ}, 0 ≤ B → (∀ x, |d x| ≤ B) → ∀ x, |d x| ≤ r * B)
    (hdD : ∀ x, |d x| ≤ D) : d = 0 := by
  have hpow : ∀ n : ℕ, ∀ x, |d x| ≤ r ^ n * D := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero, one_mul] using hdD
    | succ n ih =>
        have hnext := himprove (mul_nonneg (pow_nonneg hr0 n) hD0) ih
        intro x
        simpa only [pow_succ, mul_assoc, mul_comm r (r ^ n), mul_left_comm] using hnext x
  funext x
  have hlim : Tendsto (fun n : ℕ ↦ r ^ n * D) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D
  have hx0 : |d x| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n ↦ hpow n x)
  exact abs_eq_zero.mp (le_antisymm hx0 (abs_nonneg _))

variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]







end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

open Filter





variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution
    (R X Y : (alpha → ℝ) → alpha → ℝ) {q : alpha → ℝ} {C lam : ℝ}
    (hR_add : ∀ {f g : alpha → ℝ}, Measurable f → Measurable g →
      (∃ D, ∀ x, |f x| ≤ D) → (∃ D, ∀ x, |g x| ≤ D) → R (f + g) = R f + R g)
    (hR_bound : ∀ {f : alpha → ℝ}, Measurable f → ∀ {D : ℝ},
      (∀ x, |f x| ≤ D) → ∀ x, |R f x| ≤ D / lam)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C) (hlam : C < lam)
    (hX_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (X f))
    (hY_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (Y f))
    (hX_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |X f x| ≤ D)
    (hY_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |Y f x| ≤ D)
    (hX_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X f = R f - R (fun x ↦ q x * X f x))
    (hY_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y f = R f - R (fun x ↦ q x * Y f x))
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X f = Y f := by
  have hfBound : ∃ E : ℝ, ∀ x, |f x| ≤ E := ⟨D, hfD⟩
  have hXeq := hX_fixed hf hfBound
  have hYeq := hY_fixed hf hfBound
  have hXm : Measurable (X f) := hX_meas hf hfBound
  have hYm : Measurable (Y f) := hY_meas hf hfBound
  obtain ⟨DX, hDX⟩ := hX_bound hf hfBound
  obtain ⟨DY, hDY⟩ := hY_bound hf hfBound
  let d : alpha → ℝ := X f - Y f
  have hdMeas : Measurable d := hXm.sub hYm
  have hdBound : ∀ x, |d x| ≤ |DX| + |DY| := by
    intro x
    calc
      |d x| ≤ |X f x| + |Y f x| := abs_sub _ _
      _ ≤ DX + DY := add_le_add (hDX x) (hDY x)
      _ ≤ |DX| + |DY| := add_le_add (le_abs_self _) (le_abs_self _)
  let alpha0 : alpha := Classical.choice inferInstance
  have hC0 : 0 ≤ C := (hq0 alpha0).trans (hqC alpha0)
  have hlam0 : 0 < lam := hC0.trans_lt hlam
  have hratio0 : 0 ≤ C / lam := div_nonneg hC0 hlam0.le
  have hratio1 : C / lam < 1 := (div_lt_one hlam0).mpr hlam
  have hdEq : d = fun x ↦ -R (fun y ↦ q y * d y) x := by
    have hqXm : Measurable (fun x ↦ q x * X f x) := hq.mul hXm
    have hqYm : Measurable (fun x ↦ q x * Y f x) := hq.mul hYm
    have hqXBound : ∃ E, ∀ x, |q x * X f x| ≤ E := by
      refine ⟨C * |DX|, fun x ↦ ?_⟩
      rw [abs_mul]
      exact mul_le_mul (by simpa only [abs_of_nonneg (hq0 x)] using hqC x)
        ((hDX x).trans (le_abs_self _)) (abs_nonneg _) hC0
    have hqYBound : ∃ E, ∀ x, |q x * Y f x| ≤ E := by
      refine ⟨C * |DY|, fun x ↦ ?_⟩
      rw [abs_mul]
      exact mul_le_mul (by simpa only [abs_of_nonneg (hq0 x)] using hqC x)
        ((hDY x).trans (le_abs_self _)) (abs_nonneg _) hC0
    have hnegMeas : Measurable (fun x ↦ -(q x * Y f x)) := hqYm.neg
    have hnegBound : ∃ E, ∀ x, |-(q x * Y f x)| ≤ E := by
      simpa only [abs_neg] using hqYBound
    have hRsum := hR_add hqXm hnegMeas hqXBound hnegBound
    have hzeroMeas : Measurable (fun _ : alpha ↦ (0 : ℝ)) := measurable_const
    have hzeroBound : ∃ E : ℝ, ∀ x : alpha, |(0 : ℝ)| ≤ E :=
      ⟨0, fun _ ↦ by simp only [abs_zero, le_refl]⟩
    have hRzero : R (fun _ : alpha ↦ (0 : ℝ)) = 0 := by
      have h := hR_add hzeroMeas hzeroMeas hzeroBound hzeroBound
      rw [show (fun _ : alpha ↦ (0 : ℝ)) + (fun _ ↦ 0) = fun _ ↦ 0 by
        funext x
        simp only [Pi.add_apply, zero_add]] at h
      funext x
      have hx := congrFun h x
      simp only [Pi.add_apply] at hx
      change R (fun _ ↦ 0) x = (0 : ℝ)
      linarith only [hx]
    have hRneg : R (fun x ↦ -(q x * Y f x)) = -R (fun x ↦ q x * Y f x) := by
      have hcancel := hR_add hqYm hnegMeas hqYBound hnegBound
      rw [show (fun x ↦ q x * Y f x) + (fun x ↦ -(q x * Y f x)) = fun _ ↦ 0 by
        funext x
        simp only [Pi.add_apply, add_neg_cancel], hRzero] at hcancel
      funext x
      have hx := congrFun hcancel x
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hx ⊢
      linarith only [hx]
    funext x
    have hpoint := congrFun hRsum x
    have hnegPoint := congrFun hRneg x
    simp only [Pi.add_apply, Pi.neg_apply] at hpoint hnegPoint
    have hinput : (fun y ↦ q y * (X f y - Y f y)) =
        (fun y ↦ q y * X f y) + fun y ↦ -(q y * Y f y) := by
      funext y
      simp only [Pi.add_apply]
      ring
    have hRdiff : R (fun y ↦ q y * (X f y - Y f y)) x =
        R (fun y ↦ q y * X f y) x - R (fun y ↦ q y * Y f y) x := by
      rw [hinput, hpoint]
      have hn : R (fun y ↦ -(q y * Y f y)) x =
          -R (fun y ↦ q y * Y f y) x := by
        exact hnegPoint
      rw [hn]
      ring
    dsimp only [d]
    change X f x - Y f x = -R (fun y ↦ q y * (X f y - Y f y)) x
    calc
      X f x - Y f x =
          (R f x - R (fun y ↦ q y * X f y) x) -
            (R f x - R (fun y ↦ q y * Y f y) x) := by
        rw [congrFun hXeq x, congrFun hYeq x]
        simp only [Pi.sub_apply]
      _ = -R (fun y ↦ q y * (X f y - Y f y)) x := by
        rw [hRdiff]
        ring
  have himprove : ∀ {B : ℝ}, 0 ≤ B → (∀ x, |d x| ≤ B) →
      ∀ x, |d x| ≤ (C / lam) * B := by
    intro B hB hdB x
    have hprodMeas : Measurable (fun y ↦ q y * d y) := hq.mul hdMeas
    have hprodBound : ∀ y, |q y * d y| ≤ C * B := by
      intro y
      rw [abs_mul, abs_of_nonneg (hq0 y)]
      exact mul_le_mul (hqC y) (hdB y) (abs_nonneg _) hC0
    rw [congrFun hdEq x, abs_neg]
    calc
      |R (fun y ↦ q y * d y) x| ≤ C * B / lam :=
        hR_bound hprodMeas hprodBound x
      _ = (C / lam) * B := by field_simp
  have hd0 := function_eq_zero_of_geometric_bound hratio0 hratio1
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) himprove hdBound
  exact sub_eq_zero.mp hd0
