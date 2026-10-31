-- Prove2me | solution 1 for MarkovProcess.Semigroup.exp_smul_sub_id_apply_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T19:05:39.294998+00:00
-- url     : https://prove2.me/submissions/7261a25c-3e65-4ede-9385-426a2738e8a1

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
import Theorems.Thm_MarkovProcess_Semigroup_exp_smul_id_apply

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
theorem solution [CompleteSpace E]
    (Q : E →L[ℝ] E) (c : ℝ) (x : E) :
    exp (c • (Q - ContinuousLinearMap.id ℝ E)) x =
      ∑' n : ℕ, (Real.exp (-c) * (c ^ n / n.factorial)) • (Q ^ n) x := by
  have hcomm : Commute
      ((-c) • ContinuousLinearMap.id ℝ E) (c • Q) := by
    ext y
    simp only [mul_apply_eq_comp, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul]
    rw [mul_comm (-c) c]
  have hsplit : c • (Q - ContinuousLinearMap.id ℝ E) =
      (-c) • ContinuousLinearMap.id ℝ E + c • Q := by
    ext y
    simp only [smul_apply, add_apply,
      sub_eq_add_neg, smul_add, smul_neg, neg_smul]
    exact add_comm _ _
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm,
    mul_apply_eq_comp, exp_smul_id_apply]
  rw [exp_apply_eq_tsum]
  have hsum : Summable fun n : ℕ ↦
      ((n.factorial : ℝ)⁻¹) • ((c • Q) ^ n) x := by
    have hop : Summable fun n : ℕ ↦
        ((n.factorial : ℝ)⁻¹) • (c • Q) ^ n :=
      by
        simpa [NormedSpace.expSeries,
          ContinuousMultilinearMap.mkPiAlgebraFin_apply] using
          (NormedSpace.expSeries_summable (𝕂 := ℝ)
            (𝔸 := E →L[ℝ] E) (c • Q))
    simpa only [Function.comp_apply, smul_apply] using!
      hop.map (ContinuousLinearMap.apply ℝ E x)
        (ContinuousLinearMap.continuous _)
  change ((Real.exp (-c)) • ContinuousLinearMap.id ℝ E)
      (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ((c • Q) ^ n) x) = _
  rw [((Real.exp (-c)) • ContinuousLinearMap.id ℝ E).map_tsum hsum]
  · apply tsum_congr
    intro n
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [smul_pow_apply]
    simp only [div_eq_mul_inv, smul_smul]
    congr 1
    ring
