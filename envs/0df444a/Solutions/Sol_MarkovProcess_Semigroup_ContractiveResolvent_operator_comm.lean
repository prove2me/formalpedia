-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.operator_comm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:14:30.704605+00:00
-- url     : https://prove2.me/submissions/267aa0fc-d66f-4934-bff1-fde0c1742ac0

import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_DenseCoreConvergence_48a35d65
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic

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
theorem solution (R : ContractiveResolvent E) (α β : PositiveShift) :
    (R.operator α).comp (R.operator β) =
      (R.operator β).comp (R.operator α) := by
  by_cases hαβ : (α : ℝ) = (β : ℝ)
  · have : α = β := Subtype.ext hαβ
    subst β
    rfl
  · have hβα : (β : ℝ) - (α : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
    apply (smul_right_injective (E →L[ℝ] E) hβα)
    calc
      ((β : ℝ) - (α : ℝ)) • ((R.operator α).comp (R.operator β)) =
          R.operator α - R.operator β := (R.resolvent_identity α β).symm
      _ = ((β : ℝ) - (α : ℝ)) • ((R.operator β).comp (R.operator α)) := by
        calc
          R.operator α - R.operator β = -(R.operator β - R.operator α) := by abel
          _ = -((α : ℝ) - (β : ℝ)) •
                ((R.operator β).comp (R.operator α)) := by
            rw [R.resolvent_identity β α, neg_smul]
          _ = ((β : ℝ) - (α : ℝ)) •
                ((R.operator β).comp (R.operator α)) := by
            rw [neg_sub]
