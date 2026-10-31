-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.yosidaOperator_commute
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:15:04.037931+00:00
-- url     : https://prove2.me/submissions/97c226d8-8bd6-4058-87de-e64f4ea0e864

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaApproximation_2f7df37a
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Bounded Yosida approximations

For a contractive resolvent `R`, this file defines the bounded generator
`G_α = α (α R_α - I)` and its exponential contraction semigroup.  It also
records commutation and the exact formula on the range of a fixed resolvent.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open NormedSpace

noncomputable section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Head-class caches for the operator type.  Every repeated closed instance
search in this file is rooted at `E →L[ℝ] E`; resolving each head class once
here stops the normed-hierarchy walk on `E` from being replayed at every `•`,
`exp` and `comp`. -/







private theorem commute_smul_smul_of_comp_eq (A B : E →L[ℝ] E)
    (h : A.comp B = B.comp A) (a b : ℝ) :
    Commute (a • A) (b • B) := by
  change (a • A).comp (b • B) = (b • B).comp (a • A)
  ext x
  change a • A (b • B x) = b • B (a • A x)
  rw [map_smul, map_smul, smul_smul, smul_smul, mul_comm a b]
  exact congrArg (fun z : E ↦ (b * a) • z) (DFunLike.congr_fun h x)

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
# Bounded Yosida approximations

For a contractive resolvent `R`, this file defines the bounded generator
`G_α = α (α R_α - I)` and its exponential contraction semigroup.  It also
records commutation and the exact formula on the range of a fixed resolvent.
-/

open Filter Topology
open NormedSpace




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Head-class caches for the operator type.  Every repeated closed instance
search in this file is rooted at `E →L[ℝ] E`; resolving each head class once
here stops the normed-hierarchy walk on `E` from being replayed at every `•`,
`exp` and `comp`. -/












namespace MarkovProcess.Semigroup.ContractiveResolvent

end MarkovProcess.Semigroup.ContractiveResolvent
open MarkovProcess.Semigroup.ContractiveResolvent
theorem solution (R : ContractiveResolvent E)
    (α β : PositiveShift) (s t : NNReal) :
    Commute (R.yosidaOperator α s) (R.yosidaOperator β t) := by
  exact (commute_smul_smul_of_comp_eq _ _ (R.yosidaGenerator_commute α β).eq
    (s : ℝ) (t : ℝ)).exp
