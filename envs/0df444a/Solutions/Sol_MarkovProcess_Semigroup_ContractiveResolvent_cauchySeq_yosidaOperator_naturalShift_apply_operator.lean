-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.cauchySeq_yosidaOperator_naturalShift_apply_operator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:50:25.372958+00:00
-- url     : https://prove2.me/submissions/9cba4491-d3d7-46de-870d-5d02b21549a9

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaApproximation_2f7df37a
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_MarkovProcess_Semigroup_norm_exp_sub_exp_apply_le

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong limits of Yosida approximations

This file constructs the canonical contraction obtained by taking the strong
limit of the Yosida exponentials along the shifts `n + 1`.  Continuity of its
orbits is proved in `Semigroup/Generation.lean`, from the criterion of
`Semigroup/OrbitContinuity.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter NormedSpace Set Topology

noncomputable section

namespace MarkovProcess.Semigroup







namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





section CompleteSpace

variable [CompleteSpace E]



















end CompleteSpace

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
# Strong limits of Yosida approximations

This file constructs the canonical contraction obtained by taking the strong
limit of the Yosida exponentials along the shifts `n + 1`.  Continuity of its
orbits is proved in `Semigroup/Generation.lean`, from the criterion of
`Semigroup/OrbitContinuity.lean`.
-/

open Filter NormedSpace Set Topology










variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






variable [CompleteSpace E]

namespace MarkovProcess.Semigroup.ContractiveResolvent

end MarkovProcess.Semigroup.ContractiveResolvent
open MarkovProcess.Semigroup.ContractiveResolvent
theorem solution
    (R : ContractiveResolvent E) (mu : PositiveShift) (t : NNReal) (y : E) :
    CauchySeq (fun n ↦ R.yosidaOperator (naturalShift n) t (R.operator mu y)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [R.yosidaOperator_zero, ContinuousLinearMap.id_apply] using
      (cauchySeq_const (R.operator mu y))
  · rw [Metric.cauchySeq_iff]
    intro eps heps
    have htpos : 0 < (t : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
      (R.cauchySeq_yosidaGenerator_naturalShift_apply_operator mu y)
      (eps / (t : ℝ)) (div_pos heps htpos)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hcontract (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
        ‖exp (s • R.yosidaGenerator (naturalShift k))‖ ≤ 1 := by
      simpa only [yosidaOperator] using!
        R.norm_yosidaOperator_le_one (naturalShift k) ⟨s, hs.1⟩
    have hestimate := norm_exp_sub_exp_apply_le
      (R.yosidaGenerator (naturalShift n))
      (R.yosidaGenerator (naturalShift m))
      (R.yosidaGenerator_commute (naturalShift n) (naturalShift m))
      (NNReal.coe_nonneg t) (hcontract n) (hcontract m) (R.operator mu y)
    rw [dist_eq_norm]
    change
      ‖exp ((t : ℝ) • R.yosidaGenerator (naturalShift m)) (R.operator mu y) -
          exp ((t : ℝ) • R.yosidaGenerator (naturalShift n)) (R.operator mu y)‖ < eps
    refine lt_of_le_of_lt hestimate ?_
    rw [sub_apply, ← dist_eq_norm]
    calc
      (t : ℝ) * dist
          (R.yosidaGenerator (naturalShift m) (R.operator mu y))
          (R.yosidaGenerator (naturalShift n) (R.operator mu y))
          < (t : ℝ) * (eps / (t : ℝ)) :=
        mul_lt_mul_of_pos_left (hN m hm n hn) htpos
      _ = eps := mul_div_cancel₀ eps htpos.ne'
