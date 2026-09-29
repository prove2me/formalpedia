-- Prove2me | solution 1 for HlawkaSchatten.scalarBregman_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:56:18.934754+00:00
-- url     : https://prove2.me/submissions/2b9934db-be17-4bdb-8ee4-1c62eeb11f87

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Theorems.Thm_HlawkaSchatten_convexOn_abs_rpow
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

theorem solution {p : ℝ} (hp : 1 < p) (a b : ℝ) :
    0 ≤ scalarBregman p a b := by
  have hSupport :
      p * powerGradient p b * (a - b) ≤ |a| ^ p - |b| ^ p := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · have hSlope := (convexOn_abs_rpow hp.le).slope_le_of_hasDerivAt
          (Set.mem_univ a) (Set.mem_univ b) hab (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (div_le_iff₀ (sub_pos.mpr hab)).mp hSlope
      unfold powerGradient
      nlinarith
    · simp
    · have hSlope := (convexOn_abs_rpow hp.le).le_slope_of_hasDerivAt
          (Set.mem_univ b) (Set.mem_univ a) hba (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (le_div_iff₀ (sub_pos.mpr hba)).mp hSlope
      unfold powerGradient
      nlinarith
  rw [show scalarBregman p a b =
      (|a| ^ p - |b| ^ p - p * powerGradient p b * (a - b)) / p by
    unfold scalarBregman powerPotential
    field_simp [hp.ne']
    ]
  exact div_nonneg (sub_nonneg.mpr hSupport) (zero_lt_one.trans hp).le
