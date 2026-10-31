-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.preservesSet_yosidaOperator_of_scaledOperator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T19:11:30.233469+00:00
-- url     : https://prove2.me/submissions/13da8358-7730-4ab1-937c-2476dd8f3410

import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Definitions.Def_MarkovProcess_V3H_Semigroup_PoissonInvariant_3353c646
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_MarkovProcess_Semigroup_exp_smul_sub_id_apply_eq_tsum
import Theorems.Thm_MarkovProcess_Semigroup_summable_poissonWeight_smul_pow_apply

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
open MarkovProcess.Semigroup.ContractiveResolvent
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




















variable [CompleteSpace E]

namespace MarkovProcess.Semigroup.ContractiveResolvent

end MarkovProcess.Semigroup.ContractiveResolvent
open MarkovProcess.Semigroup.ContractiveResolvent
theorem solution
    (R : ContractiveResolvent E) (C : Set E) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (hzero : 0 ∈ C) (α : PositiveShift)
    (hQ : PreservesSet (R.scaledOperator α) C C) (t : NNReal) :
    PreservesSet (R.yosidaOperator α t) C C := by
  intro x hx
  let c : ℝ := (t : ℝ) * (α : ℝ)
  have hc : 0 ≤ c := mul_nonneg t.property α.property.le
  have hpowers : ∀ n, ((R.scaledOperator α) ^ n) x ∈ C :=
    fun n ↦ R.preservesSet_scaledOperator_pow C α hQ n hx
  have hmem := Convex.tsum_mem_of_tsum_le_one
    hclosed hconvex hzero (poissonWeight c)
    (fun n ↦ ((R.scaledOperator α) ^ n) x)
    (poissonWeight_nonneg hc) (summable_poissonWeight c)
    (by rw [tsum_poissonWeight]) hpowers
    (summable_poissonWeight_smul_pow_apply (R.scaledOperator α) c x)
  rw [yosidaOperator, yosidaGenerator, smul_smul]
  change exp (c • (R.scaledOperator α - ContinuousLinearMap.id ℝ E)) x ∈ C
  rw [exp_smul_sub_id_apply_eq_tsum]
  exact hmem
