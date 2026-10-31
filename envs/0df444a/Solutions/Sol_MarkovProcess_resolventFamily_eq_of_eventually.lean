-- Prove2me | solution 1 for MarkovProcess.resolventFamily_eq_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:30:44.862783+00:00
-- url     : https://prove2.me/submissions/1dcab140-b468-4cfa-b15f-9c022a8c2bd6

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
    (X Y : ℝ → (alpha → ℝ) → alpha → ℝ) (C : ℝ)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hlarge : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {g : alpha → ℝ}, Measurable g →
      (∃ D, ∀ x, |g x| ≤ D) → X lam g = Y lam g) {mu : ℝ} (hmu : 0 < mu)
    {f : alpha → ℝ} (hfMeas : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X mu f = Y mu f := by
  let lam : ℝ := max C mu + 1
  have hClam : C < lam := (le_max_left C mu).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have hmulam : mu < lam := (le_max_right C mu).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have hlam : 0 < lam := hmu.trans hmulam
  have hfBound : ∃ E, ∀ x, |f x| ≤ E := ⟨D, hfD⟩
  have hXm : Measurable (X mu f) := hX_meas hmu hfMeas hfBound
  have hYm : Measurable (Y mu f) := hY_meas hmu hfMeas hfBound
  have hDX := hX_bound hmu hfMeas hfD
  obtain ⟨EY, hEY⟩ := hY_bound hmu hfMeas hfBound
  let d : alpha → ℝ := X mu f - Y mu f
  have hdMeas : Measurable d := hXm.sub hYm
  have hdBound : ∀ x, |d x| ≤ D / mu + EY := by
    intro x
    exact (abs_sub _ _).trans (add_le_add (hDX x) (hEY x))
  let alpha0 : alpha := Classical.choice inferInstance
  have hDmu0 : 0 ≤ D / mu := by
    have hD0 : 0 ≤ D := (abs_nonneg (f alpha0)).trans (hfD alpha0)
    exact div_nonneg hD0 hmu.le
  have hEY0 : 0 ≤ EY := (abs_nonneg (Y mu f alpha0)).trans (hEY alpha0)
  have hdEq : d = (lam - mu) • X lam d := by
    have hXid := hX_resolvent hmu hlam hfMeas hfBound
    have hYid := hY_resolvent hmu hlam hfMeas hfBound
    have hXYf := hlarge hClam hlam hfMeas hfBound
    have hXYY := hlarge hClam hlam hYm ⟨EY, hEY⟩
    rw [← hXYf, ← hXYY] at hYid
    have hzeroMeas : Measurable (fun _ : alpha ↦ (0 : ℝ)) := measurable_const
    have hzeroBound : ∃ E : ℝ, ∀ x : alpha, |(0 : ℝ)| ≤ E :=
      ⟨0, fun _ ↦ by simp only [abs_zero, le_refl]⟩
    have hXzero : X lam (fun _ ↦ 0) = 0 := by
      have h := hX_add hlam hzeroMeas hzeroMeas hzeroBound hzeroBound
      have hzadd : (fun _ : alpha ↦ (0 : ℝ)) + (fun _ ↦ 0) = fun _ ↦ 0 := by
        funext x
        simp only [Pi.add_apply, zero_add]
      rw [hzadd] at h
      funext x
      have hx := congrFun h x
      simp only [Pi.add_apply] at hx
      change X lam (fun _ ↦ 0) x = (0 : ℝ)
      linarith only [hx]
    have hnegBound : ∃ E, ∀ x, |-(Y mu f x)| ≤ E :=
      ⟨EY, fun x ↦ by simpa only [abs_neg] using hEY x⟩
    have hnegMeas : Measurable (fun x ↦ -(Y mu f x)) := hYm.neg
    have hsum := hX_add hlam hXm hnegMeas ⟨D / mu, hDX⟩ hnegBound
    have hneg : X lam (fun x ↦ -(Y mu f x)) = -X lam (Y mu f) := by
      have hcancel := hX_add hlam hYm hnegMeas ⟨EY, hEY⟩ hnegBound
      rw [show (Y mu f + fun x ↦ -(Y mu f x)) = fun _ ↦ 0 by
        funext x
        simp only [Pi.add_apply, add_neg_cancel]] at hcancel
      rw [hXzero] at hcancel
      funext x
      have hx := congrFun hcancel x
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hx ⊢
      linarith only [hx]
    funext x
    have hsumx := congrFun hsum x
    have hnegx := congrFun hneg x
    have hXx := congrFun hXid x
    have hYx := congrFun hYid x
    dsimp only [d]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsumx hXx hYx ⊢
    change X lam (fun z ↦ -(Y mu f z)) x = -X lam (Y mu f) x at hnegx
    rw [show X mu f - Y mu f = X mu f + fun z ↦ -(Y mu f z) by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply]
      ring]
    rw [hsumx, hnegx]
    rw [hXx, hYx]
    ring
  have hratio0 : 0 ≤ (lam - mu) / lam :=
    div_nonneg (sub_nonneg.mpr hmulam.le) hlam.le
  have hratio1 : (lam - mu) / lam < 1 := (div_lt_one hlam).mpr (sub_lt_self lam hmu)
  have himprove : ∀ {B : ℝ}, 0 ≤ B → (∀ x, |d x| ≤ B) →
      ∀ x, |d x| ≤ ((lam - mu) / lam) * B := by
    intro B hB hdB x
    rw [congrFun hdEq x, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hmulam.le)]
    calc
      (lam - mu) * |X lam d x| ≤ (lam - mu) * (B / lam) :=
        mul_le_mul_of_nonneg_left (hX_bound hlam hdMeas hdB x)
          (sub_nonneg.mpr hmulam.le)
      _ = ((lam - mu) / lam) * B := by field_simp
  have hd0 := function_eq_zero_of_geometric_bound hratio0 hratio1
    (add_nonneg hDmu0 hEY0) himprove hdBound
  exact sub_eq_zero.mp hd0
