-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_map_headTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:42:22.122996+00:00
-- url     : https://prove2.me/submissions/f065ddb4-b97a-43a4-a039-622c1c37cd2f

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelConcatenation_cb54f8d1
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Concatenating finite-time kernels at an ordered cut

This file factors an ordered finite-dimensional transition law at a designated observation
time.  The future factor is the finite-time kernel at the corresponding relative times, started
from the terminal coordinate of the past.  This is finite-dimensional kernel infrastructure and
does not assert a path-space or conditional Markov theorem.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess



namespace FiniteOrderedTimes







end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha]





















private theorem measurable_headTail {n : ℕ} :
    Measurable (fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path)) := by
  apply Measurable.prodMk (measurable_pi_apply 0)
  exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply i.succ

omit [MeasurableSpace alpha] in
private theorem headTail_finCons {n : ℕ} (z : alpha × (Fin n → alpha)) :
    ((fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path))
      (@Fin.cons n (fun _ ↦ alpha) z.1 z.2)) = z := by
  apply Prod.ext
  · rfl
  · funext i
    rfl











namespace IsConservative






end IsConservative

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
# Concatenating finite-time kernels at an ordered cut

This file factors an ordered finite-dimensional transition law at a designated observation
time.  The future factor is the finite-time kernel at the corresponding relative times, started
from the terminal coordinate of the past.  This is finite-dimensional kernel infrastructure and
does not assert a path-space or conditional Markov theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory






variable {alpha : Type*} [MeasurableSpace alpha]































namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution (P : SubMarkovKernelSemigroup alpha) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) :
    (finiteTimeKernel P times).map
        (fun path ↦ (path 0, Fin.tail path)) =
      P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
        (finiteTimeKernel P times.relativeTail) := by
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
  · have hcomp :
        (fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path)) ∘
            (fun z : alpha × (Fin n → alpha) ↦
              @Fin.cons n (fun _ ↦ alpha) z.1 z.2) = id := by
          funext z
          exact headTail_finCons z
    rw [hcomp, Kernel.map_id]
  · exact measurable_pi_iff.mpr fun i ↦ Fin.cases measurable_fst
      (fun j ↦ (measurable_pi_apply j).comp measurable_snd) i
  · exact measurable_headTail
