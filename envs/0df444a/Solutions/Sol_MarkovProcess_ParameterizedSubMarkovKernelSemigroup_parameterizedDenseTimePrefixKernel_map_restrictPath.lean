-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimePrefixKernel_map_restrictPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:06:05.629492+00:00
-- url     : https://prove2.me/submissions/73049ced-7178-42d6-864d-665d9f90c7f6

import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
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
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized kernels on finite prefixes of a countable time enumeration

This file constructs jointly measurable kernels on the first `n` points of an arbitrary
enumeration. Coordinates remain in enumeration order; the enumeration need not be monotone in
physical time. Fiberwise conservativity is used only for Markovness and prefix consistency.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]











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
# Parameterized kernels on finite prefixes of a countable time enumeration

This file constructs jointly measurable kernels on the first `n` points of an arbitrary
enumeration. Coordinates remain in enumeration order; the enumeration need not be monotone in
physical time. Fiberwise conservativity is used only for Markovness and prefix consistency.
-/

open MeasureTheory ProbabilityTheory



variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]









namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
theorem solution
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) {m n : ℕ} (h : m ≤ n) :
    P.parameterizedDenseTimePrefixKernel e ι m =
      (P.parameterizedDenseTimePrefixKernel e ι n).map
        (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) := by
  apply Kernel.ext
  intro q
  obtain ⟨theta, x⟩ := q
  rw [Kernel.map_apply _
      (FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h)),
    parameterizedDenseTimePrefixKernel_apply,
    parameterizedDenseTimePrefixKernel_apply]
  have hrestrict := congrArg (fun K : Kernel alpha (Fin m → alpha) ↦ K x)
    ((hP theta).denseTimePrefixKernel_map_restrictPath
      (P.toSubMarkovKernelSemigroup theta) e ι h)
  change (P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι m x =
    ((P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι n).map
      (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) x at hrestrict
  rw [Kernel.map_apply _
    (FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h))] at hrestrict
  exact hrestrict
