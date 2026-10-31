-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.c0Semigroup_operator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:39:48.83056+00:00
-- url     : https://prove2.me/submissions/3870b912-1a89-4be9-ad8a-35a7e5fe1509

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0_dfad2e28
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology
open scoped ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]





variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)









section Feller

variable [LocallyCompactSpace α] [T2Space α]









end Feller

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/

open Topology
open scoped ZeroAtInfty



variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]





variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)



namespace MarkovProcess.SubMarkovKernelSemigroup
end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
@[simp]
theorem solution (hTime : P.HasContinuousC0Orbits hC0) (t : NNReal) :
    (P.c0Semigroup hC0 hTime) t = P.c0Operator hC0 t :=
  rfl
