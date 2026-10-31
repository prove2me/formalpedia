-- Prove2me | solution 1 for MarkovProcess.Semigroup.ContractiveResolvent.generatedSemigroup_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:14:16.954736+00:00
-- url     : https://prove2.me/submissions/84e54d61-9590-4290-afcc-0ccb9c268446

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
@[simp]
theorem solution (R : ContractiveResolvent E) (t : NNReal) :
    R.generatedSemigroup t = R.yosidaStrongLimit t :=
  rfl
