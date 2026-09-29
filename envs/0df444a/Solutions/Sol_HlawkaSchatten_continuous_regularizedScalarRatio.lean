-- Prove2me | solution 1 for HlawkaSchatten.continuous_regularizedScalarRatio
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:03:53.511694+00:00
-- url     : https://prove2.me/submissions/d2ee283f-d7f0-480b-825b-cdb04da0ceb0

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Theorems.Thm_HlawkaSchatten_continuous_signedPower
import Theorems.Thm_HlawkaSchatten_strictMono_signedPower
import Theorems.Thm_HlawkaSchatten_tendsto_scalarRatio_one
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

/-- The regularized scalar ratio is continuous at its removable point. -/
theorem continuousAt_regularizedScalarRatio_one {p : ℝ} (hp : 1 < p) :
    ContinuousAt (regularizedScalarRatio p) 1 := by
  have hfun : regularizedScalarRatio p = Function.update (scalarRatio p) 1
      (2 * (p - 1) / p ^ 2) := by
    funext t
    by_cases ht : t = 1
    · subst t
      simp [regularizedScalarRatio]
    · simp [regularizedScalarRatio, ht]
  rw [hfun]
  exact continuousAt_update_same.mpr (tendsto_scalarRatio_one hp)

theorem regularizedScalarRatio_of_ne (p : ℝ) {t : ℝ} (ht : t ≠ 1) :
    regularizedScalarRatio p t = scalarRatio p t := by
  simp [regularizedScalarRatio, ht]

/-- The Mazur denominator vanishes only at the removable point. -/
theorem scalarMazur_eq_one_iff {p : ℝ} (hp : 0 < p) (t : ℝ) :
    scalarMazur p t = 1 ↔ t = 1 := by
  have hmono : StrictMono (signedPower (p / 2)) :=
    strictMono_signedPower (half_pos hp)
  constructor
  · intro h
    apply hmono.injective
    simpa [scalarMazur, signedPower] using h
  · rintro rfl
    simp [scalarMazur, signedPower]

theorem scalarMazur_sub_one_ne_zero {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 1) :
    scalarMazur p t - 1 ≠ 0 := by
  rw [sub_ne_zero]
  exact (scalarMazur_eq_one_iff hp t).not.mpr ht

theorem solution {p : ℝ} (hp : 1 < p) :
    Continuous (regularizedScalarRatio p) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 1
  · subst t
    exact continuousAt_regularizedScalarRatio_one hp
  · have hratio : ContinuousAt (scalarRatio p) t := by
      unfold scalarRatio
      have hmazur : ContinuousAt (scalarMazur p) t := by
        exact (continuous_signedPower (half_pos (zero_lt_one.trans hp))).continuousAt
      have hbregman : ContinuousAt (fun x : ℝ ↦ scalarBregman p x 1) t := by
        unfold scalarBregman powerPotential
        fun_prop (disch := positivity)
      exact hbregman.div ((hmazur.sub continuousAt_const).pow 2)
        (pow_ne_zero 2 (scalarMazur_sub_one_ne_zero (zero_lt_one.trans hp) ht))
    apply hratio.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht] with x hx
    exact regularizedScalarRatio_of_ne p hx
