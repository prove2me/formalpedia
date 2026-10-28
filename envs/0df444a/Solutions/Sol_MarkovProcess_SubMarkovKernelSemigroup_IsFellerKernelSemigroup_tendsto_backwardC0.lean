-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_backwardC0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:12:44.122712+00:00
-- url     : https://prove2.me/submissions/23809048-c40a-40ba-b96d-62889f2a8687

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
import Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_tendsto_apply_of_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess



namespace FiniteOrderedTimes



@[simp]
theorem relativeTail_apply {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (i : Fin n) :
    times.relativeTail i = times i.succ - times 0 :=
  rfl
end FiniteOrderedTimes
end MarkovProcess
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


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



/-- The backward recursion for a singleton family is one Feller-semigroup application. -/
@[simp]
theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.backwardC0_zero
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    (times : FiniteOrderedTimes 1) (factors : Fin 1 → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0) (factors 0) :=
  rfl

/-- At a successor length, the backward recursion multiplies the first factor by the recursively
evolved relative tail before applying the first transition. -/
@[simp]
theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.backwardC0_succ
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 2))
    (factors : Fin (n + 2) → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0)
      (factors 0 * hP.backwardC0 times.relativeTail (Fin.tail factors)) :=
  rfl


theorem solution
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes (n + 1)}
    {times0 : FiniteOrderedTimes (n + 1)}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun a ↦ hP.backwardC0 (times a) factors) l
      (nhds (hP.backwardC0 times0 factors)) := by
  induction n with
  | zero =>
      simp only [backwardC0_zero]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto (ht 0) tendsto_const_nhds
  | succ n ih =>
      have htail : ∀ i, Tendsto (fun a ↦ (times a).relativeTail i) l
          (nhds (times0.relativeTail i)) := by
        intro i
        simpa only [FiniteOrderedTimes.relativeTail_apply] using
          (ht i.succ).sub (ht 0)
      have hinner := ih htail (Fin.tail factors)
      simp only [backwardC0_succ]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto (ht 0)
        (tendsto_const_nhds.mul hinner)
