-- Prove2me | solution 1 for HlawkaSchatten.powerGradient_eq_signedPower
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:26:26.714044+00:00
-- url     : https://prove2.me/submissions/c0f9f25f-7f11-45ce-866f-2a3ac048e4ce

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

theorem solution (p x : ℝ) :
    powerGradient p x = signedPower (p - 1) x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have habs : 0 < |x| := abs_pos.mpr hx
    have hpow : |x| ^ (p - 1) = |x| ^ (p - 2) * |x| := by
      calc
        |x| ^ (p - 1) = |x| ^ ((p - 2) + 1) := by congr 1; ring
        _ = |x| ^ (p - 2) * |x| ^ (1 : ℝ) := Real.rpow_add habs _ _
        _ = |x| ^ (p - 2) * |x| := by rw [Real.rpow_one]
    change |x| ^ (p - 2) * x = (SignType.sign x : ℝ) * |x| ^ (p - 1)
    rw [hpow]
    calc
      |x| ^ (p - 2) * x =
          |x| ^ (p - 2) * ((SignType.sign x : ℝ) * |x|) := by rw [sign_mul_abs]
      _ = (SignType.sign x : ℝ) * (|x| ^ (p - 2) * |x|) := by ring
