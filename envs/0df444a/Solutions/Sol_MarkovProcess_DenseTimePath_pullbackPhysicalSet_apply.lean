-- Prove2me | solution 1 for MarkovProcess.DenseTimePath.pullbackPhysicalSet_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:45:13.434197+00:00
-- url     : https://prove2.me/submissions/232a9a80-b4a9-43ce-ad37-7843735cae5d

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

noncomputable section

namespace DenseTime

open SubMarkovKernelSemigroup





end DenseTime

namespace DenseTimePath

open SubMarkovKernelSemigroup

variable {alpha : Type*}





variable [MeasurableSpace alpha]





end DenseTimePath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/





open SubMarkovKernelSemigroup

variable {alpha : Type*}



namespace MarkovProcess.DenseTimePath
end MarkovProcess.DenseTimePath
open MarkovProcess.DenseTimePath
@[simp]
theorem solution (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) (t : I) :
    pullbackPhysicalSet I path t = path (DenseTime.physicalSetEquiv I t) := rfl
