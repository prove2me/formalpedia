-- Prove2me | solution 1 for HlawkaSchatten.scalarMazur_distance_sq_normalize
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:27:00.958425+00:00
-- url     : https://prove2.me/submissions/422fc6a1-b399-47a0-95af-997f045cab40

import Definitions.Def_HlawkaSchatten_ScalarBregman
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

































































/-- Signed powers have their expected homogeneity for a positive scalar. -/
theorem signedPower_mul_of_pos (q x : ℝ) {c : ℝ} (hc : 0 < c) :
    signedPower q (c * x) = c ^ q * signedPower q x := by
  simp only [signedPower, sign_mul, sign_pos hc, one_mul, abs_mul,
    abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg x)]
  ring

/-- The scalar Mazur map has degree `p / 2`. -/
theorem scalarMazur_mul_of_pos (p x : ℝ) {c : ℝ} (hc : 0 < c) :
    scalarMazur p (c * x) = c ^ (p / 2) * scalarMazur p x := by
  exact signedPower_mul_of_pos (p / 2) x hc









end HlawkaSchatten

theorem solution (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (scalarMazur p a - scalarMazur p b) ^ 2 =
      |b| ^ p * (scalarMazur p (a / b) - 1) ^ 2 := by
  have hab : b * (a / b) = a := by field_simp
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hA : scalarMazur p (-a) =
        (-b) ^ (p / 2) * scalarMazur p (a / b) := by
      simpa [hb, hab] using scalarMazur_mul_of_pos p ((-a) / (-b)) (neg_pos.mpr hbneg)
    have hB : scalarMazur p (-b) = (-b) ^ (p / 2) := by
      simpa [scalarMazur, signedPower] using
        scalarMazur_mul_of_pos p 1 (neg_pos.mpr hbneg)
    have hpow : ((-b) ^ (p / 2)) ^ 2 = (-b) ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (neg_nonneg.mpr hbneg.le)]
      congr 1
      ring
    rw [abs_of_neg hbneg]
    calc
      (scalarMazur p a - scalarMazur p b) ^ 2 =
          (scalarMazur p (-a) - scalarMazur p (-b)) ^ 2 := by simp; ring
      _ = (-b) ^ p * (scalarMazur p (a / b) - 1) ^ 2 := by
        rw [hA, hB, ← hpow]
        ring
  · have hA : scalarMazur p a = b ^ (p / 2) * scalarMazur p (a / b) := by
      simpa [hab] using scalarMazur_mul_of_pos p (a / b) hbpos
    have hB : scalarMazur p b = b ^ (p / 2) := by
      simpa [scalarMazur, signedPower] using scalarMazur_mul_of_pos p 1 hbpos
    have hpow : (b ^ (p / 2)) ^ 2 = b ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbpos.le]
      congr 1
      ring
    rw [abs_of_pos hbpos, hA, hB, ← hpow]
    ring
