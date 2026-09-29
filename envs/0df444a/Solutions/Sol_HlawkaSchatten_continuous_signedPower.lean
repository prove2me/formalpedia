-- Prove2me | solution 1 for HlawkaSchatten.continuous_signedPower
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:02:21.182524+00:00
-- url     : https://prove2.me/submissions/651270f6-6228-49b8-a957-8fa9f9da97cc

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

theorem solution {q : ℝ} (hq : 0 < q) : Continuous (signedPower q) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, signedPower_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun y : ℝ ↦ |y| ^ q) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun y : ℝ ↦ |y| ^ q) 0 :=
        continuous_abs.continuousAt.rpow_const (Or.inr hq.le)
      simpa [Real.zero_rpow hq.ne'] using hcont.tendsto
    apply hlim.congr'
    apply Eventually.of_forall
    intro y
    by_cases hy : y = 0
    · subst y
      simp [signedPower, Real.zero_rpow hq.ne']
    · rcases lt_or_gt_of_ne hy with hyneg | hypos
      · simp only [signedPower, sign_neg hyneg, SignType.coe_neg, SignType.coe_one,
          neg_mul, one_mul, norm_neg, Real.norm_eq_abs]
        exact (abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) q)).symm
      · simp only [signedPower, sign_pos hypos, SignType.coe_one, one_mul, Real.norm_eq_abs]
        exact (abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) q)).symm
  · have hsign : ContinuousAt (fun y : ℝ ↦ (SignType.sign y : ℝ)) x := by
      have hcoe : Continuous fun s : SignType ↦ (s : ℝ) :=
        continuous_of_discreteTopology
      exact hcoe.continuousAt.comp (continuousAt_sign_of_ne_zero hx)
    exact hsign.mul (continuous_abs.continuousAt.rpow_const (Or.inl (abs_ne_zero.mpr hx)))
