-- Prove2me | solution 1 for MarkovProcess.Semigroup.summable_poissonWeight_smul_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:16:48.529237+00:00
-- url     : https://prove2.me/submissions/fc5d2318-d629-44cc-ba99-8b7257397502

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





private theorem smul_pow_apply (c : ℝ) (Q : E →L[ℝ] E) (n : ℕ) (x : E) :
    ((c • Q) ^ n) x = c ^ n • (Q ^ n) x := by
  induction n generalizing x with
  | zero => simp only [pow_zero, one_apply_eq_self, one_smul]
  | succ n ih =>
      rw [pow_succ, pow_succ, mul_apply_eq_comp, ih,
        smul_apply, map_smul, smul_smul]
      rw [mul_comm (c ^ n) c]
      rw [pow_succ, mul_apply_eq_comp]













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
theorem solution
    [CompleteSpace E] (Q : E →L[ℝ] E) (c : ℝ) (x : E) :
    Summable fun n : ℕ ↦ poissonWeight c n • (Q ^ n) x := by
  have hop : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • (c • Q) ^ n := by
    simpa [NormedSpace.expSeries,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ)
        (𝔸 := E →L[ℝ] E) (c • Q))
  have happ : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • ((c • Q) ^ n) x := by
    simpa only [Function.comp_apply, smul_apply] using!
      hop.map (ContinuousLinearMap.apply ℝ E x)
        (ContinuousLinearMap.continuous _)
  have hscaled := happ.map
    ((Real.exp (-c)) • ContinuousLinearMap.id ℝ E)
    (ContinuousLinearMap.continuous _)
  apply hscaled.congr
  intro n
  simp only [Function.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, poissonWeight, div_eq_mul_inv,
    smul_pow_apply]
  congr 1
  ring
