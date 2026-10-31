-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.lintegral_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:05:10.640911+00:00
-- url     : https://prove2.me/submissions/8c9e0a45-1740-4905-a516-20bd844c7b8d

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
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂P theta (s + t) x =
      ∫⁻ y, ∫⁻ z, f z ∂P theta t y ∂P theta s x := by
  rw [P.add, Kernel.lintegral_comp _ _ _ hf]
