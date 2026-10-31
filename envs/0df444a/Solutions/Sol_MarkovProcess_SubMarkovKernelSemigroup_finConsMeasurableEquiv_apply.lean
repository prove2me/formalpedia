-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.finConsMeasurableEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:41:29.163028+00:00
-- url     : https://prove2.me/submissions/3f323103-761d-4623-b144-a8cef29be151

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
@[simp]
theorem solution (n : ℕ) (z : alpha × (Fin n → alpha)) :
    finConsMeasurableEquiv n z = Fin.cons z.1 z.2 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl
