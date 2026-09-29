-- Prove2me | solution 1 for HlawkaSchatten.strictConvexOn_abs_rpow
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T00:38:31.85579+00:00
-- url     : https://prove2.me/submissions/dc88c491-c60a-466b-91ab-50ab974518e3

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Theorems.Thm_HlawkaSchatten_powerGradient_eq_signedPower
import Theorems.Thm_HlawkaSchatten_strictMono_signedPower
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

theorem solution {p : ℝ} (hp : 1 < p) :
    StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hcont : Continuous (fun x : ℝ ↦ |x| ^ p) := by
    have hdiff : Differentiable ℝ (fun x : ℝ ↦ ‖x‖ ^ p) :=
      differentiable_norm_rpow hp
    simpa only [Real.norm_eq_abs] using hdiff.continuous
  apply StrictMono.strictConvexOn_univ_of_deriv hcont
  have hderiv : deriv (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * powerGradient p x := by
    funext x
    rw [(hasDerivAt_abs_rpow x hp).deriv]
    unfold powerGradient
    ring
  rw [hderiv]
  have hgrad : StrictMono (powerGradient p) := by
    intro x y hxy
    rw [powerGradient_eq_signedPower, powerGradient_eq_signedPower]
    exact strictMono_signedPower (sub_pos.mpr hp) hxy
  exact hgrad.const_mul (zero_lt_one.trans hp)
