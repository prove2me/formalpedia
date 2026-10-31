-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_coordinateProduct_finiteTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:39:45.257935+00:00
-- url     : https://prove2.me/submissions/b816bd3a-1a69-4ab0-a9f3-1ec353196bf6

import Mathlib
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

open Filter Topology
namespace MarkovProcess.Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem p2m_inline_tendsto_apply_of_opNorm_le_one {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i ↦ T i w) l (nhds (Tlim w)))
    (hv : Tendsto v l (nhds w)) :
    Tendsto (fun i ↦ T i (v i)) l (nhds (Tlim w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) hε2,
    Metric.tendsto_nhds.mp hTlim (ε / 2) hε2] with i hvi hTi
  have hcontract : dist (T i (v i)) (T i w) ≤ dist (v i) w := by
    calc
      dist (T i (v i)) (T i w) ≤ ‖T i‖ * dist (v i) w := (T i).dist_le_opNorm _ _
      _ ≤ 1 * dist (v i) w := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist (v i) w := one_mul _
  calc
    dist (T i (v i)) (Tlim w) ≤ dist (T i (v i)) (T i w) + dist (T i w) (Tlim w) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hvi) hTi
    _ = ε := add_halves ε

end MarkovProcess.Semigroup


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

Main results: `p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup`,
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

/-- Convergence in the `C₀` norm is uniform convergence of the evaluated functions. -/
theorem tendstoUniformly_apply_of_tendsto {F : iota → C₀(alpha, ℝ)} {f : C₀(alpha, ℝ)}
    (h : Tendsto F l (nhds f)) : TendstoUniformly (fun i x ↦ F i x) (fun x ↦ f x) l :=
  ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mp h

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

Main results: `p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup`,
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
open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}
private theorem p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup
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
      exact Semigroup.p2m_inline_tendsto_apply_of_opNorm_le_one
        (fun i ↦ (hP i).c0Semigroup (times 0)) (hQ.c0Semigroup (times 0))
        (fun i ↦ factors 0 * (hP i).backwardC0 times.relativeTail (Fin.tail factors))
        (factors 0 * hQ.backwardC0 times.relativeTail (Fin.tail factors))
        (fun i ↦ ((hP i).c0Semigroup).norm_operator_le_one _) (hconv (times 0) _)
        (tendsto_const_nhds.mul (ih times.relativeTail (Fin.tail factors)))

end MarkovProcess.SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup
theorem solution
    {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hQ : Q.IsFellerKernelSemigroup)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    TendstoUniformly
      (fun i x ↦ ∫ path, ∏ j, factors j (path j) ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, ∏ j, factors j (path j) ∂finiteTimeKernel Q times x) l := by
  have h := tendstoUniformly_apply_of_tendsto
    (p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup hP hQ hconv times factors)
  simpa only [IsFellerKernelSemigroup.p2m_embedded_2a9d6bc61fa8399e] using h
