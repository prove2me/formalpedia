-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_finiteSetLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:23:47.305977+00:00
-- url     : https://prove2.me/submissions/c7b05f87-634e-4d9a-aefb-a0db2b9002b5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
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
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]



















namespace IsConservative









end IsConservative
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
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]






















namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (I : Finset NNReal) (x : α) :
    IsProbabilityMeasure (finiteSetLaw P I x) := by
  let : IsMarkovKernel (finiteSetKernel P I) := hP.isMarkovKernel_finiteSetKernel P I
  exact IsMarkovKernel.isProbabilityMeasure x
