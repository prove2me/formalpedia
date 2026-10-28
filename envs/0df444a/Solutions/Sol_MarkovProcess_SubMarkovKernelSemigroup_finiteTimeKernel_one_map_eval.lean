-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:01:18.892777+00:00
-- url     : https://prove2.me/submissions/a946443c-450a-4876-bf1e-c56d9b1e2142

import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-time kernels on strictly ordered time families

A conservative sub-Markov kernel semigroup determines probability kernels on finite coordinate
spaces.  The construction itself does not use a conservativity witness: it recursively samples the
first observation and then the relative tail.  Conservativity is used only to prove that the
resulting kernels are Markov kernels.

This file constructs finite-dimensional kernels only.  It makes no path-space, projectivity,
conservativity, or stochastic-process existence claim beyond the explicitly stated results.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory





variable {α : Type*} [MeasurableSpace α]














@[simp]
theorem solution (P : SubMarkovKernelSemigroup α)
    (times : FiniteOrderedTimes 1) :
    (finiteTimeKernel P times).map (fun path ↦ path 0) = P (times 0) := by
  let : IsFiniteKernel (P (times 0)) := (P.isSubMarkovKernel (times 0)).isFiniteKernel
  let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
    by rw [finiteTimeKernel_zero]; infer_instance
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
  rw [← Kernel.map_comp_right]
  · have hcomp :
        ((fun path : Fin 1 → α ↦ path 0) ∘
          fun z : α × (Fin 0 → α) ↦
            @Fin.cons 0 (fun _ : Fin 1 ↦ α) z.1 z.2) = Prod.fst := by
        funext z
        rfl
    rw [hcomp, ← Kernel.fst_eq]
    exact Kernel.fst_compProd _ _
  · exact measurable_finCons
  · exact measurable_pi_apply 0
