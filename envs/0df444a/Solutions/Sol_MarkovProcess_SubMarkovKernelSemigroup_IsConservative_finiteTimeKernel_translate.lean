-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_translate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:00:43.649134+00:00
-- url     : https://prove2.me/submissions/d145a403-ccb0-4599-9e23-5076931fa4a3

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
import Mathlib.Probability.Kernel.Composition.KernelLemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
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
theorem translate_apply {n : ℕ} (s : NNReal) (times : FiniteOrderedTimes n) (i : Fin n) :
    times.translate s i = s + times i :=
  rfl



/-- Translation does not change the relative tail of a finite ordered time family. -/
@[simp]
theorem relativeTail_translate {n : ℕ} (s : NNReal)
    (times : FiniteOrderedTimes (n + 1)) :
    (times.translate s).relativeTail = times.relativeTail := by
  apply DFunLike.ext _ _
  intro i
  exact add_tsub_add_eq_tsub_left s (times i.succ) (times 0)
end FiniteOrderedTimes
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-time kernels

This file proves the finite-dimensional translation identity for a conservative transition-kernel
semigroup. It is ordinary kernel infrastructure and makes no path-space or process-existence claim.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


variable {W X Y Z : Type*}
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem compProd_prodMkLeft_comp (κ : Kernel X Y) (η : Kernel Y Z)
    (ξ : Kernel W X) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ξ] :
    (κ.comp ξ) ⊗ₖ Kernel.prodMkLeft W η = (κ ⊗ₖ Kernel.prodMkLeft X η).comp ξ := by
  rw [Kernel.compProd_prodMkLeft_eq_comp, Kernel.compProd_prodMkLeft_eq_comp,
    Kernel.comp_assoc]


variable {α : Type*} [MeasurableSpace α]


theorem solution (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (s : NNReal) {n : ℕ} (times : FiniteOrderedTimes n) :
    finiteTimeKernel P (times.translate s) = (finiteTimeKernel P times).comp (P s) := by
  induction n with
  | zero =>
      let : IsMarkovKernel (P s) := hP.isMarkovKernel s
      rw [finiteTimeKernel_zero, finiteTimeKernel_zero, Kernel.const_comp']
  | succ n ih =>
      let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ]
      simp only [FiniteOrderedTimes.translate_apply, FiniteOrderedTimes.relativeTail_translate]
      rw [P.add s (times 0), Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, compProd_prodMkLeft_comp, Kernel.map_comp]
