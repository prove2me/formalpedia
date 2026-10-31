-- Prove2me | solution 1 for MarkovProcess.Semigroup.exp_smul_id_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T19:02:14.012726+00:00
-- url     : https://prove2.me/submissions/aa6c47e0-965e-4ffe-b1a7-d52a3545008e

import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Definitions.Def_MarkovProcess_V3H_Semigroup_PoissonInvariant_3353c646
import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Poisson invariance of bounded Yosida exponentials

This file proves the uniformization argument: a normalized resolvent preserving
a closed convex set containing zero has Yosida exponentials preserving that set.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open NormedSpace

noncomputable section

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



















namespace ContractiveResolvent

variable [CompleteSpace E]





end ContractiveResolvent

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Poisson invariance of bounded Yosida exponentials

This file proves the uniformization argument: a normalized resolvent preserving
a closed convex set containing zero has Yosida exponentials preserving that set.
-/

open Filter Set Topology
open NormedSpace



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace MarkovProcess.Semigroup

end MarkovProcess.Semigroup
open MarkovProcess.Semigroup
theorem solution (a : ℝ) (x : E) :
    exp (a • ContinuousLinearMap.id ℝ E) x = Real.exp a • x := by
  have hmap := NormedSpace.map_exp
    (algebraMap ℝ (E →L[ℝ] E))
    (continuous_algebraMap ℝ (E →L[ℝ] E)) a
  rw [← Real.exp_eq_exp_ℝ] at hmap
  have halg : algebraMap ℝ (E →L[ℝ] E) a =
      a • ContinuousLinearMap.id ℝ E := by
    ext y
    simp only [ContinuousLinearMap.algebraMap_apply,
      smul_apply, ContinuousLinearMap.id_apply]
  rw [halg] at hmap
  rw [← hmap]
  exact ContinuousLinearMap.algebraMap_apply _ _
