-- Prove2me | solution 1 for HlawkaSchatten.scalarBregman_pos
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T00:48:27.894583+00:00
-- url     : https://prove2.me/submissions/d6d1cd22-2beb-4f37-9c86-e8b4145683ef

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Theorems.Thm_HlawkaSchatten_strictConvexOn_abs_rpow
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

theorem solution {p : ℝ} (hp : 1 < p) {a b : ℝ} (hab : a ≠ b) :
    0 < scalarBregman p a b := by
  have hSupport :
      p * powerGradient p b * (a - b) < |a| ^ p - |b| ^ p := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hSlope := (strictConvexOn_abs_rpow hp).slope_lt_of_hasDerivAt
          (Set.mem_univ a) (Set.mem_univ b) hlt (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hSlope
      unfold powerGradient
      nlinarith
    · exact (hab heq).elim
    · have hSlope := (strictConvexOn_abs_rpow hp).lt_slope_of_hasDerivAt
          (Set.mem_univ b) (Set.mem_univ a) hgt (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (lt_div_iff₀ (sub_pos.mpr hgt)).mp hSlope
      unfold powerGradient
      nlinarith
  rw [show scalarBregman p a b =
      (|a| ^ p - |b| ^ p - p * powerGradient p b * (a - b)) / p by
    unfold scalarBregman powerPotential
    field_simp [hp.ne']]
  exact div_pos (sub_pos.mpr hSupport) (zero_lt_one.trans hp)
