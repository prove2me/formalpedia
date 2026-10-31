-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_denseTimePrefixKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:23:39.677348+00:00
-- url     : https://prove2.me/submissions/be030609-c767-436d-a15e-f5aaa74193d2

import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernels on finite prefixes of a countable time enumeration

This file constructs the finite-dimensional kernel on the first `n` points of an arbitrary
enumeration, with coordinates retained in enumeration order. The enumeration need not respect
the order of physical time.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]

















namespace IsConservative







end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernels on finite prefixes of a countable time enumeration

This file constructs the finite-dimensional kernel on the first `n` points of an arbitrary
enumeration, with coordinates retained in enumeration order. The enumeration need not respect
the order of physical time.
-/

open MeasureTheory ProbabilityTheory



variable {D α : Type*} [MeasurableSpace α]




















namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) (x : α) :
    IsProbabilityMeasure (denseTimePrefixKernel P e ι n x) := by
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  exact IsMarkovKernel.isProbabilityMeasure x
