-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.add_apply_prime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:01:51.933046+00:00
-- url     : https://prove2.me/submissions/41f0dee2-be27-467d-877c-918ee135ced7

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurably parameterized sub-Markov kernel semigroups

This file packages sub-Markov kernel semigroups depending measurably on a parameter. The
measurability field is joint in parameter, time, and starting state, with carrier ordering
`Theta × (NNReal × alpha)`. Each fixed-parameter slice is an ordinary
`SubMarkovKernelSemigroup`.

No parameter family is selected here, and no concrete coefficient, domain, Feller, conservativity,
or stochastic-process assertion is made.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory



namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]





variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)





























end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurably parameterized sub-Markov kernel semigroups

This file packages sub-Markov kernel semigroups depending measurably on a parameter. The
measurability field is joint in parameter, time, and starting state, with carrier ordering
`Theta × (NNReal × alpha)`. Each fixed-parameter slice is an ordinary
`SubMarkovKernelSemigroup`.

No parameter family is selected here, and no concrete coefficient, domain, Feller, conservativity,
or stochastic-process assertion is made.
-/

open Set
open scoped ENNReal ProbabilityTheory



open MeasureTheory ProbabilityTheory




variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]





variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)





















namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
theorem solution (theta : Theta) (s t : NNReal) (x : alpha)
    {u : Set alpha} (hu : MeasurableSet u) :
    P theta (s + t) x u = ∫⁻ y, P theta t y u ∂P theta s x := by
  rw [P.add, Kernel.comp_apply' _ _ _ hu]
