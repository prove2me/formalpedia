-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedNextObservationJoint_fst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:36.891984+00:00
-- url     : https://prove2.me/submissions/516fef60-c3e3-41fb-a7a9-d4cc8eba5875

import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeConditionalKernel_90321c52
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedDenseTimePrefixKernel_map_restrictPath

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional kernels for parameterized finite dense-time prefixes

This file disintegrates the jointly parameterized law of a finite dense-time prefix and its next
observation. The resulting conditional kernel is one jointly measurable version. No comparison
with separately chosen fixed-parameter conditional versions is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



variable [StandardBorelSpace alpha] [Nonempty alpha]









end
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
# Conditional kernels for parameterized finite dense-time prefixes

This file disintegrates the jointly parameterized law of a finite dense-time prefix and its next
observation. The resulting conditional kernel is one jointly measurable version. No comparison
with separately chosen fixed-parameter conditional versions is asserted.
-/

open MeasureTheory ProbabilityTheory



variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



variable [StandardBorelSpace alpha] [Nonempty alpha]

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup
end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
omit [StandardBorelSpace alpha] [Nonempty alpha] in

theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedNextObservationJoint e iota n).fst =
      P.parameterizedDenseTimePrefixKernel e iota n := by
  rw [parameterizedNextObservationJoint, Kernel.mapOfMeasurable_eq_map, Kernel.fst_eq,
    ← Kernel.map_comp_right]
  · change
      (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
        P.parameterizedDenseTimePrefixKernel e iota n
    calc
      (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
          (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
            (FiniteOrderedTimes.restrictPath
              (Fin.castLEOrderEmb (Nat.le_succ n))) := by
        congr 1
        funext path i
        exact DenseTimeHistory.splitLast_fst_apply n path i
      _ = P.parameterizedDenseTimePrefixKernel e iota n :=
        (P.parameterizedDenseTimePrefixKernel_map_restrictPath
          hP e iota (Nat.le_succ n)).symm
  · exact (DenseTimeHistory.splitLast n).measurable
  · exact measurable_fst
