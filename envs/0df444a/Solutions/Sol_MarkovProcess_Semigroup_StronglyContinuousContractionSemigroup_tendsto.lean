-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:16:26.544114+00:00
-- url     : https://prove2.me/submissions/f8270604-5720-459a-8ac6-50b2a711bb88

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

namespace MarkovProcess.Semigroup



namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





variable (S : StronglyContinuousContractionSemigroup E)

















theorem continuousAt (t : NNReal) (x : E) : ContinuousAt (fun s ↦ S s x) t :=
  (S.continuous x).continuousAt







end StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

open Filter Topology





variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





variable (S : StronglyContinuousContractionSemigroup E)



















namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution (t : NNReal) (x : E) :
    Tendsto (fun s ↦ S s x) (nhds t) (nhds (S t x)) :=
  S.continuousAt t x
