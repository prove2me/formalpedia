-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.exists_norm_yosidaStrongLimit_apply_sub_on_range_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:14:09.247396+00:00
-- url     : https://prove2.me/submissions/20157370-022e-4e95-9216-22497351d988

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
import Mathlib.Analysis.Calculus.Deriv.Mul
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
# Generation of a contraction semigroup from a contractive resolvent

This file packages the strong limit of the Yosida exponential approximations
as a strongly continuous contraction semigroup.  Strong continuity at zero is
first proved on the range of one resolvent and then extended by density.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter NormedSpace Set Topology

noncomputable section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]













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
# Generation of a contraction semigroup from a contractive resolvent

This file packages the strong limit of the Yosida exponential approximations
as a strongly continuous contraction semigroup.  Strong continuity at zero is
first proved on the range of one resolvent and then extended by density.
-/

open Filter NormedSpace Set Topology




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace MarkovProcess.Semigroup.ContractiveResolvent

end MarkovProcess.Semigroup.ContractiveResolvent
open MarkovProcess.Semigroup.ContractiveResolvent
theorem solution
    (R : ContractiveResolvent E) (mu : PositiveShift) (y : E) :
    ∃ C : ℝ, ∀ t : NNReal,
      ‖R.yosidaStrongLimit t (R.operator mu y) - R.operator mu y‖ ≤ (t : ℝ) * C := by
  have hgen := R.cauchySeq_yosidaGenerator_naturalShift_apply_operator mu y
  obtain ⟨C, hC⟩ := hgen.isBounded_range.exists_norm_le
  refine ⟨C, fun t ↦ ?_⟩
  refine le_of_tendsto
    ((R.tendsto_yosidaOperator_naturalShift_apply t (R.operator mu y)).sub
      tendsto_const_nhds).norm ?_
  exact Eventually.of_forall fun n ↦ by
    have hcontract : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
        ‖exp (s • R.yosidaGenerator (naturalShift n))‖ ≤ 1 := by
      intro s hs
      have h := R.norm_yosidaOperator_le_one (naturalShift n) ⟨s, hs.1⟩
      simp only [yosidaOperator] at h
      exact h
    exact (norm_exp_apply_sub_le (R.yosidaGenerator (naturalShift n))
      (NNReal.coe_nonneg t) hcontract (R.operator mu y)).trans
        (mul_le_mul_of_nonneg_left
          (hC _ ⟨n, rfl⟩) (NNReal.coe_nonneg t))
