-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.tendsto_backwardC0_of_tendsto_c0Semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:39:24.649127+00:00
-- url     : https://prove2.me/submissions/dda36efa-4137-4297-9783-cbb5d722b2aa

import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Theorems.Thm_MarkovProcess_Semigroup_tendsto_apply_of_opNorm_le_one

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence of the backward `C₀` recursion along a family of semigroups

The backward recursion of `Feller/BackwardC0Recursion.lean` evolves a nonempty ordered family of
one-coordinate `C₀` factors through the transitions of one Feller kernel semigroup.  Here the
family of times and the factors are held fixed and the *semigroup* varies along a filter: if the
`C₀` semigroups converge strongly, so does the backward recursion, in the `C₀` norm.  The
induction is one line per step: contractivity makes the outer transition insensitive to the
error accumulated by the inner one.

Since the `C₀` norm is the supremum norm, this is exactly convergence of the coordinate-product
integrals against the finite-time kernels, uniformly in the starting point.

Main results: `tendsto_backwardC0_of_tendsto_c0Semigroup`,
`tendstoUniformly_integral_coordinateProduct_finiteTimeKernel`.

The factors and the observation times are fixed; nothing is asserted when they vary along the
filter as well, and no rate of convergence is claimed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess

section Uniform

variable {alpha : Type*} [TopologicalSpace alpha] {iota : Type*} {l : Filter iota}



end Uniform

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}





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
# Convergence of the backward `C₀` recursion along a family of semigroups

The backward recursion of `Feller/BackwardC0Recursion.lean` evolves a nonempty ordered family of
one-coordinate `C₀` factors through the transitions of one Feller kernel semigroup.  Here the
family of times and the factors are held fixed and the *semigroup* varies along a filter: if the
`C₀` semigroups converge strongly, so does the backward recursion, in the `C₀` norm.  The
induction is one line per step: contractivity makes the outer transition insensitive to the
error accumulated by the inner one.

Since the `C₀` norm is the supremum norm, this is exactly convergence of the coordinate-product
integrals against the finite-time kernels, uniformly in the starting point.

Main results: `tendsto_backwardC0_of_tendsto_c0Semigroup`,
`tendstoUniformly_integral_coordinateProduct_finiteTimeKernel`.

The factors and the observation times are fixed; nothing is asserted when they vary along the
filter as well, and no rate of convergence is claimed.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}

namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution
    {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hQ : Q.IsFellerKernelSemigroup)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun i ↦ (hP i).backwardC0 times factors) l
      (nhds (hQ.backwardC0 times factors)) := by
  induction n with
  | zero =>
      simpa only [IsFellerKernelSemigroup.backwardC0_zero] using hconv (times 0) (factors 0)
  | succ n ih =>
      simp only [IsFellerKernelSemigroup.backwardC0_succ]
      exact Semigroup.tendsto_apply_of_opNorm_le_one
        (fun i ↦ (hP i).c0Semigroup (times 0)) (hQ.c0Semigroup (times 0))
        (fun i ↦ factors 0 * (hP i).backwardC0 times.relativeTail (Fin.tail factors))
        (factors 0 * hQ.backwardC0 times.relativeTail (Fin.tail factors))
        (fun i ↦ ((hP i).c0Semigroup).norm_operator_le_one _) (hconv (times 0) _)
        (tendsto_const_nhds.mul (ih times.relativeTail (Fin.tail factors)))
