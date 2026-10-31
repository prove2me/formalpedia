-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.tendsto_scaledOperator_apply_on_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:46.858301+00:00
-- url     : https://prove2.me/submissions/f89149b6-119e-450b-9f61-5342035362e1

import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_DenseCoreConvergence_48a35d65
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MarkovProcess_Semigroup_ContractiveResolvent_scaledOperator_apply_sub_on_range

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Contractive resolvent families

This module packages the elementary resolvent identity, the Hille--Yosida
bound, and dense range, then derives normalization at large positive shifts.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

namespace MarkovProcess.Semigroup



namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]















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
# Contractive resolvent families

This module packages the elementary resolvent identity, the Hille--Yosida
bound, and dense range, then derives normalization at large positive shifts.
-/

open Filter Topology





variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]











namespace MarkovProcess.Semigroup.ContractiveResolvent

end MarkovProcess.Semigroup.ContractiveResolvent
open MarkovProcess.Semigroup.ContractiveResolvent
theorem solution (R : ContractiveResolvent E)
    (μ : PositiveShift) (y : E) :
    Tendsto (fun α : PositiveShift ↦ R.scaledOperator α (R.operator μ y))
      atTop (nhds (R.operator μ y)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ α : PositiveShift,
      ‖R.scaledOperator α (R.operator μ y) - R.operator μ y‖ ≤
        ‖(μ : ℝ) • R.operator μ y - y‖ * (α : ℝ)⁻¹ := by
    intro α
    rw [R.scaledOperator_apply_sub_on_range α μ y]
    calc
      ‖R.operator α ((μ : ℝ) • R.operator μ y - y)‖ ≤
          ‖R.operator α‖ * ‖(μ : ℝ) • R.operator μ y - y‖ :=
        (R.operator α).le_opNorm _
      _ ≤ (α : ℝ)⁻¹ * ‖(μ : ℝ) • R.operator μ y - y‖ :=
        mul_le_mul_of_nonneg_right (R.opNorm_le_inv α) (norm_nonneg _)
      _ = ‖(μ : ℝ) • R.operator μ y - y‖ * (α : ℝ)⁻¹ := mul_comm _ _
  simpa only [dist_eq_norm] using
    squeeze_zero (fun α => norm_nonneg _) hbound
      (tendsto_const_mul_positiveShift_inv_atTop_zero
        ‖(μ : ℝ) • R.operator μ y - y‖)
