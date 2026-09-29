-- Prove2me | solution 1 for HlawkaSchatten.scalarBregman_two_sided_of_compactified_bounds
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:27:44.392256+00:00
-- url     : https://prove2.me/submissions/4df5ae7a-a8d8-4954-968a-e0bf35b40f9d

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Theorems.Thm_HlawkaSchatten_powerGradient_eq_signedPower
import Theorems.Thm_HlawkaSchatten_scalarMazur_distance_sq_normalize
import Theorems.Thm_HlawkaSchatten_strictMono_signedPower
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The scalar Bregman--Mazur ratio

This file starts the compact scalar-reduction layer of the Schatten Hlawka
argument.  The raw quotient has a removable singularity at `t = 1`; the
regularized version installs its second-order limiting value.
-/


open Filter Set
open scoped OnePoint Topology

open HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Scalar power Bregman data

These are the scalar objects used in the first layer of the audited
Bregman--Mazur proof. The normalization of `powerPotential` is important:
its derivative is the signed `(p - 1)`-power with no extra factor of `p`.
-/

namespace HlawkaSchatten

open Filter
open scoped Topology















@[simp]
theorem powerGradient_zero (p : ℝ) : powerGradient p 0 = 0 := by
  simp [powerGradient]





@[simp]
theorem scalarBregman_self (p a : ℝ) : scalarBregman p a a = 0 := by
  simp [scalarBregman]







@[simp]
theorem powerPotential_neg (p x : ℝ) : powerPotential p (-x) = powerPotential p x := by
  simp [powerPotential]

@[simp]
theorem powerGradient_neg (p x : ℝ) : powerGradient p (-x) = -powerGradient p x := by
  rw [powerGradient_eq_signedPower, powerGradient_eq_signedPower, signedPower_neg]



@[simp]
theorem scalarBregman_neg (p a b : ℝ) :
    scalarBregman p (-a) (-b) = scalarBregman p a b := by
  simp only [scalarBregman, powerPotential_neg, powerGradient_neg]
  ring

































/-- The normalized power gradient has degree `p - 1`. -/
theorem powerGradient_mul_of_pos (p x : ℝ) {c : ℝ} (hc : 0 < c) :
    powerGradient p (c * x) = c ^ (p - 1) * powerGradient p x := by
  have hpow : c ^ (p - 1) = c ^ (p - 2) * c := by
    calc
      c ^ (p - 1) = c ^ ((p - 2) + 1) := by congr 1; ring
      _ = c ^ (p - 2) * c ^ (1 : ℝ) := Real.rpow_add hc _ _
      _ = c ^ (p - 2) * c := by rw [Real.rpow_one]
  simp only [powerGradient, abs_mul, abs_of_pos hc,
    Real.mul_rpow hc.le (abs_nonneg x), hpow]
  ring



/-- The scalar Bregman divergence has degree `p` under positive common scaling. -/
theorem scalarBregman_mul_of_pos (p a b : ℝ) {c : ℝ} (hc : 0 < c) :
    scalarBregman p (c * a) (c * b) = c ^ p * scalarBregman p a b := by
  have hpow : c ^ p = c ^ (p - 1) * c := by
    calc
      c ^ p = c ^ ((p - 1) + 1) := by congr 1; ring
      _ = c ^ (p - 1) * c ^ (1 : ℝ) := Real.rpow_add hc _ _
      _ = c ^ (p - 1) * c := by rw [Real.rpow_one]
  rw [scalarBregman, powerPotential_mul_of_pos p a hc,
    powerPotential_mul_of_pos p b hc, powerGradient_mul_of_pos p b hc]
  unfold scalarBregman
  rw [hpow]
  ring



end HlawkaSchatten

@[simp]
theorem compactifiedScalarRatio_coe (p t : ℝ) :
    compactifiedScalarRatio p (t : OnePoint ℝ) = regularizedScalarRatio p t := rfl

@[simp]
theorem compactifiedScalarRatio_infty (p : ℝ) :
    compactifiedScalarRatio p ∞ = 1 / p := rfl

theorem regularizedScalarRatio_of_ne (p : ℝ) {t : ℝ} (ht : t ≠ 1) :
    regularizedScalarRatio p t = scalarRatio p t := by
  simp [regularizedScalarRatio, ht]

/-- Normalization of a scalar Bregman divergence by a nonzero second argument. -/
theorem scalarBregman_normalize (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    scalarBregman p a b = |b| ^ p * scalarBregman p (a / b) 1 := by
  have hab : b * (a / b) = a := by field_simp
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hscale := scalarBregman_mul_of_pos p ((-a) / (-b)) 1 (neg_pos.mpr hbneg)
    simpa [abs_of_neg hbneg, hb, hab] using hscale
  · have hscale := scalarBregman_mul_of_pos p (a / b) 1 hbpos
    simpa [abs_of_pos hbpos, hb, hab] using hscale

/-- The normalized scalar quotient is exactly `scalarRatio (a / b)`. -/
theorem scalarBregman_div_mazur_sq_eq_scalarRatio (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    scalarBregman p a b / (scalarMazur p a - scalarMazur p b) ^ 2 =
      scalarRatio p (a / b) := by
  rw [scalarBregman_normalize p a hb, scalarMazur_distance_sq_normalize p a hb]
  unfold scalarRatio
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos (abs_pos.mpr hb) p).ne'

theorem scalarBregman_zero_right {p : ℝ} (hp : 0 < p) (a : ℝ) :
    scalarBregman p a 0 = (1 / p) * (scalarMazur p a - scalarMazur p 0) ^ 2 := by
  rw [scalarMazur_zero, sub_zero, scalarMazur_sq hp]
  unfold scalarBregman powerPotential
  simp [hp.ne']
  ring

theorem solution {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M) (a b : ℝ) :
    m * (scalarMazur p a - scalarMazur p b) ^ 2 ≤ scalarBregman p a b ∧
      scalarBregman p a b ≤ M * (scalarMazur p a - scalarMazur p b) ^ 2 := by
  by_cases hab : a = b
  · subst b
    simp
  by_cases hb : b = 0
  · subst b
    rw [scalarBregman_zero_right (zero_lt_one.trans hp)]
    have hendpoint := hbound (∞ : OnePoint ℝ)
    simp only [compactifiedScalarRatio_infty] at hendpoint
    have hsq : 0 ≤ (scalarMazur p a - scalarMazur p 0) ^ 2 := sq_nonneg _
    constructor <;> nlinarith
  · have ht : a / b ≠ 1 := by
      intro heq
      apply hab
      field_simp [hb] at heq
      linarith
    have hdist : 0 < (scalarMazur p a - scalarMazur p b) ^ 2 := by
      apply sq_pos_of_ne_zero
      rw [sub_ne_zero]
      exact (strictMono_signedPower
        (half_pos (zero_lt_one.trans hp))).injective.ne hab
    have hfactor : scalarBregman p a b =
        scalarRatio p (a / b) * (scalarMazur p a - scalarMazur p b) ^ 2 := by
      apply (div_eq_iff hdist.ne').mp
      exact scalarBregman_div_mazur_sq_eq_scalarRatio p a hb
    have hratio := hbound (a / b : OnePoint ℝ)
    rw [compactifiedScalarRatio_coe, regularizedScalarRatio_of_ne p ht] at hratio
    rw [hfactor]
    constructor <;> nlinarith
