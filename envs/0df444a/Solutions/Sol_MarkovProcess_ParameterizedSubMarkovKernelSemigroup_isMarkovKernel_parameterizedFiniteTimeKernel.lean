-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isMarkovKernel_parameterizedFiniteTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:02:06.333273+00:00
-- url     : https://prove2.me/submissions/54af772e-a93a-4e1f-acfd-9ebc28a6a45b

import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeKernel_da0af7ef
import Definitions.Def_MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized finite-time kernels

This file constructs the finite-dimensional kernel at a fixed strictly ordered time family for a
measurably parameterized sub-Markov semigroup. The construction recursively carries the parameter
through the augmented state kernel. Fiberwise conservativity is used only for the Markov-kernel
property.

The slice theorem identifies evaluation at a parameter and start with the existing
nonparameterized finite-time kernel of the fixed-parameter semigroup. No path-space or
stochastic-process existence claim is made here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



















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
# Parameterized finite-time kernels

This file constructs the finite-dimensional kernel at a fixed strictly ordered time family for a
measurably parameterized sub-Markov semigroup. The construction recursively carries the parameter
through the augmented state kernel. Fiberwise conservativity is used only for the Markov-kernel
property.

The slice theorem identifies evaluation at a parameter and start with the existing
nonparameterized finite-time kernel of the fixed-parameter semigroup. No path-space or
stochastic-process existence claim is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory



variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]









namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup
end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    IsMarkovKernel (P.parameterizedFiniteTimeKernel times) := by
  induction n with
  | zero =>
      rw [parameterizedFiniteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsMarkovKernel (P.augmentedKernel (times 0)) :=
        P.isMarkovKernel_augmentedKernel hP (times 0)
      let : IsMarkovKernel (P.parameterizedFiniteTimeKernel times.relativeTail) :=
        ih times.relativeTail
      rw [parameterizedFiniteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      exact Kernel.IsMarkovKernel.map _ measurable_finCons_snd
