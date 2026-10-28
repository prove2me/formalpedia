-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.backwardC0_apply_eq_integral_finiteTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:12:12.256495+00:00
-- url     : https://prove2.me/submissions/dd282236-9e9b-4084-b431-5492f4ec63fa

import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_finiteTimeKernel_one_map_eval
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Backward `C₀` recursion for finite Feller transitions

An ordered nonempty family of one-coordinate `C₀` factors determines a backward semigroup
recursion: evolve the last factors relative to the first time, multiply by the first factor, and
then evolve from the starting state to the first time.  The recursion varies continuously in the
`C₀` norm when every ordered observation time converges.

This file contains only the analytic recursion and its continuity.  Its identification with an
integral against a finite-time kernel is in `Feller/BackwardC0Integral.lean`; no statement about
path space is proved here.
-/

open Filter Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



/-- The backward recursion for a singleton family is one Feller-semigroup application. -/
@[simp]
theorem IsFellerKernelSemigroup.backwardC0_zero
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    (times : FiniteOrderedTimes 1) (factors : Fin 1 → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0) (factors 0) :=
  rfl

/-- At a successor length, the backward recursion multiplies the first factor by the recursively
evolved relative tail before applying the first transition. -/
@[simp]
theorem IsFellerKernelSemigroup.backwardC0_succ
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 2))
    (factors : Fin (n + 2) → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0)
      (factors 0 * hP.backwardC0 times.relativeTail (Fin.tail factors)) :=
  rfl
end SubMarkovKernelSemigroup
end MarkovProcess

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

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]





variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)









section Feller

variable [LocallyCompactSpace α] [T2Space α]







@[simp]
theorem IsFellerKernelSemigroup.c0Semigroup_apply_apply
    {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)
    (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    hP.c0Semigroup t f x = kernelIntegral (P t) f x :=
  rfl
end Feller
end SubMarkovKernelSemigroup
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-time integral represented by the backward `C₀` recursion

The backward Feller-semigroup recursion for a nonempty ordered family of `C₀` factors evaluates
to the integral of their coordinate product against the corresponding finite-time kernel.  The
proof follows the recursive kernel construction and uses composition-product integration.

No conservativity assumption is needed: sub-Markov finite-time kernels already give finite
measures, which suffice for bounded integrability.  This is an analytic identification only; no
statement about path space is proved here, and the process itself is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory ZeroAtInfty


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProduct
    {Omega : Type*} [MeasurableSpace Omega] {n : ℕ}
    (factors : Fin n → C₀(alpha, ℝ)) (eval : Omega → Fin n → alpha)
    (heval : Measurable eval) (mu : Measure Omega) [IsFiniteMeasure mu] :
    Integrable (fun omega ↦ ∏ i, factors i (eval omega i)) mu := by
  refine Integrable.of_bound ?_ (∏ i, ‖factors i‖) ?_
  · exact
    (Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
      ((factors i).measurable.comp
        ((measurable_pi_apply i).comp heval)).stronglyMeasurable).aestronglyMeasurable
  · filter_upwards [] with omega
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
    intro i _
    simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using!
      (factors i).toBCF.norm_coe_le_norm (eval omega i)

omit [TopologicalSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha]
  [T2Space alpha] in
private theorem isFiniteKernel_finiteTimeKernel
    (P : SubMarkovKernelSemigroup alpha) {n : ℕ}
    (times : FiniteOrderedTimes n) : IsFiniteKernel (finiteTimeKernel P times) := by
  induction n with
  | zero =>
      rw [finiteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (finiteTimeKernel P times.relativeTail) :=
        ih times.relativeTail
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      infer_instance


theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) (x : alpha) :
    hP.backwardC0 times factors x =
      ∫ path, ∏ i, factors i (path i) ∂finiteTimeKernel P times x := by
  induction n generalizing x with
  | zero =>
      rw [hP.backwardC0_zero, hP.c0Semigroup_apply_apply]
      rw [← finiteTimeKernel_one_map_eval P times]
      unfold kernelIntegral
      rw [Kernel.map_apply _ (measurable_pi_apply 0)]
      rw [integral_map (measurable_pi_apply 0).aemeasurable
        (factors 0).measurable.stronglyMeasurable.aestronglyMeasurable]
      congr 1
      funext path
      rw [Fin.prod_univ_one]
  | succ n ih =>
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (finiteTimeKernel P times.relativeTail) :=
        isFiniteKernel_finiteTimeKernel P times.relativeTail
      let productTest : (Fin (n + 2) → alpha) → ℝ :=
        fun path ↦ ∏ i, factors i (path i)
      have hProductTest : StronglyMeasurable productTest := by
        exact Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
          ((factors i).measurable.comp (measurable_pi_apply i)).stronglyMeasurable
      rw [hP.backwardC0_succ, hP.c0Semigroup_apply_apply]
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      unfold kernelIntegral
      change (∫ y, _ ∂P (times 0) x) =
        ∫ path, productTest path ∂(Kernel.map
          (P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
            (finiteTimeKernel P times.relativeTail))
          (fun z ↦ Fin.cons z.1 z.2)) x
      rw [Kernel.map_apply _ measurable_finCons]
      rw [integral_map measurable_finCons.aemeasurable
        hProductTest.aestronglyMeasurable]
      dsimp only [productTest]
      rw [integral_compProd (integrable_coordinateProduct factors
        (fun z ↦ Fin.cons z.1 z.2) measurable_finCons _)]
      have heta : ∀ a, Kernel.prodMkLeft alpha
          (finiteTimeKernel P times.relativeTail) (x, a) =
            finiteTimeKernel P times.relativeTail a := by
        intro a
        ext s hs
        rw [Kernel.prodMkLeft_apply']
      simp_rw [heta]
      apply integral_congr_ae
      filter_upwards [] with a
      change factors 0 a * hP.backwardC0 times.relativeTail (Fin.tail factors) a = _
      have hprod : (fun b : Fin (n + 1) → alpha ↦
          ∏ i, factors i
            (@Fin.cons (n + 1) (fun _ : Fin (n + 2) ↦ alpha) a b i)) =
          fun b ↦ factors 0 a * ∏ i, (Fin.tail factors) i (b i) := by
        funext b
        rw [Fin.prod_univ_succ]
        rfl
      rw [hprod, integral_const_mul,
        ih times.relativeTail (Fin.tail factors) a]
