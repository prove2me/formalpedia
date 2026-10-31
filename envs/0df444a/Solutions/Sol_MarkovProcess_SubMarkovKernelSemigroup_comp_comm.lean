-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:39:55.705487+00:00
-- url     : https://prove2.me/submissions/9046eb23-9b0b-4a39-99e8-2d0c7b574067

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory



namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]





variable (P : SubMarkovKernelSemigroup α)























namespace IsConservative



end IsConservative

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
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/

open Set
open scoped ENNReal ProbabilityTheory



open MeasureTheory ProbabilityTheory




variable {α : Type*} [MeasurableSpace α]





variable (P : SubMarkovKernelSemigroup α)









namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution (s t : NNReal) : (P t).comp (P s) = (P s).comp (P t) := by
  rw [← P.add, ← P.add, add_comm]
