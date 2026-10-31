-- Prove2me | solution 1 for MarkovProcess.Semigroup.PreservesSet.comp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:15:21.118347+00:00
-- url     : https://prove2.me/submissions/7d1252a6-c180-4c66-a238-090da20ff776

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
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
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology

noncomputable section

namespace MarkovProcess.Semigroup



namespace PreservesSet

variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}







end PreservesSet

end MarkovProcess.Semigroup

namespace Convex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end Convex

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
open MarkovProcess.Semigroup.PreservesSet
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology






variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}



namespace MarkovProcess.Semigroup.PreservesSet
end MarkovProcess.Semigroup.PreservesSet
open MarkovProcess.Semigroup.PreservesSet
theorem solution {S : F → G} {T : E → F}
    (hS : PreservesSet S D K) (hT : PreservesSet T C D) :
    PreservesSet (S ∘ T) C K :=
  fun _ hx ↦ hS (hT hx)
