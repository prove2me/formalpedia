-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.scaledOperator_apply_sub_on_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:14:38.410404+00:00
-- url     : https://prove2.me/submissions/9b92ac5c-fe70-476f-8d2d-7cbec2b31bde

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
theorem solution (R : ContractiveResolvent E)
    (α β : PositiveShift) (y : E) :
    R.scaledOperator α (R.operator β y) - R.operator β y =
      R.operator α ((β : ℝ) • R.operator β y - y) := by
  have h := DFunLike.congr_fun (R.resolvent_identity α β) y
  change
    R.operator α y - R.operator β y =
      ((β : ℝ) - (α : ℝ)) • R.operator α (R.operator β y) at h
  change
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
      R.operator α ((β : ℝ) • R.operator β y - y)
  rw [map_sub, map_smul]
  change
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
      (β : ℝ) • R.operator α (R.operator β y) - R.operator α y
  calc
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
        (α : ℝ) • R.operator α (R.operator β y) +
          (R.operator α y - R.operator β y) - R.operator α y := by abel
    _ = (α : ℝ) • R.operator α (R.operator β y) +
          ((β : ℝ) - (α : ℝ)) • R.operator α (R.operator β y) -
            R.operator α y := by rw [h]
    _ = (β : ℝ) • R.operator α (R.operator β y) - R.operator α y := by module
