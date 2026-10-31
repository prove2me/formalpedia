-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.pullbackFiniteSetTranslate_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:46:20.697337+00:00
-- url     : https://prove2.me/submissions/350b379b-dd33-4a4b-bc58-dbf2d7e6c7a8

import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelShift_4030eb49
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section





















namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]



end IsConservative

end
end SubMarkovKernelSemigroup

namespace DenseTime



end DenseTime
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

open MeasureTheory ProbabilityTheory













namespace MarkovProcess.SubMarkovKernelSemigroup
end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
@[simp]
theorem solution {alpha : Type*} (s : NNReal) (I : Finset NNReal)
    (path : finiteSetTranslate s I → alpha) (t : I) :
    pullbackFiniteSetTranslate s I path t = path (finiteSetTranslateEquiv s I t) :=
  rfl
