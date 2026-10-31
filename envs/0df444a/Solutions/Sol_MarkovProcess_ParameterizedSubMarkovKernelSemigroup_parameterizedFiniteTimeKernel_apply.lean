-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedFiniteTimeKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:06:39.275696+00:00
-- url     : https://prove2.me/submissions/0fe96b31-e9c0-4c6d-8e6d-271a253f755b

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











private theorem isFiniteKernel_parameterizedFiniteTimeKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    IsFiniteKernel (P.parameterizedFiniteTimeKernel times) := by
  induction n with
  | zero =>
      rw [parameterizedFiniteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      have hParameterState : IsSubMarkovKernel (P.parameterStateKernel (times 0)) :=
        fun q ↦ by
          rw [parameterStateKernel_apply]
          exact P.isSubMarkovKernel q.1 (times 0) q.2
      let : IsFiniteKernel (P.parameterStateKernel (times 0)) :=
        hParameterState.isFiniteKernel
      let : IsFiniteKernel (P.augmentedKernel (times 0)) := by
        rw [augmentedKernel]
        infer_instance
      let : IsFiniteKernel (P.parameterizedFiniteTimeKernel times.relativeTail) :=
        ih times.relativeTail
      rw [parameterizedFiniteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      infer_instance

private theorem isFiniteKernel_finiteTimeKernel
    (Q : SubMarkovKernelSemigroup alpha)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    IsFiniteKernel (Q.finiteTimeKernel times) := by
  induction n with
  | zero =>
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsFiniteKernel (Q (times 0)) :=
        (Q.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (Q.finiteTimeKernel times.relativeTail) :=
        ih times.relativeTail
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ,
        Kernel.mapOfMeasurable_eq_map]
      infer_instance

private theorem augmentedKernel_apply_eq_map
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (theta : Theta) (t : NNReal) (x : alpha) :
    P.augmentedKernel t (theta, x) = (P theta t x).map (Prod.mk theta) := by
  have hParameterState : IsSubMarkovKernel (P.parameterStateKernel t) := fun q ↦ by
    rw [parameterStateKernel_apply]
    exact P.isSubMarkovKernel q.1 t q.2
  let : IsFiniteKernel (P.parameterStateKernel t) := hParameterState.isFiniteKernel
  let : IsFiniteKernel (P theta t) := (P.isSubMarkovKernel theta t).isFiniteKernel
  rw [augmentedKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    parameterStateKernel_apply, Measure.dirac_prod]



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
    {n : ℕ} (times : FiniteOrderedTimes n) (theta : Theta) (x : alpha) :
    P.parameterizedFiniteTimeKernel times (theta, x) =
      SubMarkovKernelSemigroup.finiteTimeKernel
        (P.toSubMarkovKernelSemigroup theta) times x := by
  induction n generalizing theta x with
  | zero =>
      rw [parameterizedFiniteTimeKernel_zero,
        SubMarkovKernelSemigroup.finiteTimeKernel_zero,
        Kernel.const_apply, Kernel.const_apply]
  | succ n ih =>
      let Q := P.toSubMarkovKernelSemigroup theta
      let : IsFiniteKernel (P.augmentedKernel (times 0)) := by
        have hParameterState : IsSubMarkovKernel (P.parameterStateKernel (times 0)) :=
          fun q ↦ by
            rw [parameterStateKernel_apply]
            exact P.isSubMarkovKernel q.1 (times 0) q.2
        let : IsFiniteKernel (P.parameterStateKernel (times 0)) :=
          hParameterState.isFiniteKernel
        rw [augmentedKernel]
        infer_instance
      let : IsFiniteKernel (P.parameterizedFiniteTimeKernel times.relativeTail) :=
        isFiniteKernel_parameterizedFiniteTimeKernel P times.relativeTail
      let : IsFiniteKernel (Q (times 0)) := Q.isSubMarkovKernel (times 0) |>.isFiniteKernel
      let : IsFiniteKernel
          (SubMarkovKernelSemigroup.finiteTimeKernel Q times.relativeTail) :=
        isFiniteKernel_finiteTimeKernel Q times.relativeTail
      ext s hs
      rw [parameterizedFiniteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply' _ measurable_finCons_snd _ hs,
        Kernel.compProd_apply (hs.preimage measurable_finCons_snd),
        augmentedKernel_apply_eq_map, MeasureTheory.lintegral_map]
      · rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ,
          Kernel.mapOfMeasurable_eq_map]
        rw [Kernel.map_apply' _ measurable_finCons _ hs,
          Kernel.compProd_apply (hs.preimage measurable_finCons)]
        simp_rw [Kernel.prodMkLeft_apply', ih times.relativeTail theta]
        rfl
      · exact Kernel.measurable_kernel_prodMk_left'
          (hs.preimage measurable_finCons_snd) (theta, x)
      · exact measurable_const.prodMk measurable_id
