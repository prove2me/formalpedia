-- Prove2me | solution 1 for HlawkaSchatten.powerGradient_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:55:23.225155+00:00
-- url     : https://prove2.me/submissions/937d2afa-64a0-461f-a587-a27ea824cceb

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign

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


open Filter
open scoped Topology

open HlawkaSchatten

@[simp]
theorem powerGradient_zero (p : ℝ) : powerGradient p 0 = 0 := by
  simp [powerGradient]

@[simp]
theorem powerPotential_zero (p : ℝ) : powerPotential p 0 = 0 := by
  by_cases hp : p = 0 <;> simp [powerPotential, hp]

theorem solution {p : ℝ} (hp : 0 < p) (x : ℝ) :
    powerGradient p x * x = p * powerPotential p x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have ha : 0 < |x| := abs_pos.mpr hx
    unfold powerGradient powerPotential
    have hs : x * x = |x| ^ (2 : ℕ) := by
      nlinarith [sq_abs x]
    rw [mul_assoc, hs]
    rw [show |x| ^ (2 : ℕ) = |x| ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add ha]
    rw [show p - 2 + 2 = p by ring]
    field_simp [hp.ne']
