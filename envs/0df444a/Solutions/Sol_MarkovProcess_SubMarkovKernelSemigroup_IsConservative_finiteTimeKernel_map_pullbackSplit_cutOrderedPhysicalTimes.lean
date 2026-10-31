-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_pullbackSplit_cutOrderedPhysicalTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:15:58.425825+00:00
-- url     : https://prove2.me/submissions/e2590fe0-a1e5-4748-9e74-0daf95f4e74c

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
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
import Theorems.Thm_MarkovProcess_MixedPastFuture_cutOrderedPhysicalTimes_initialSegment
import Theorems.Thm_MarkovProcess_MixedPastFuture_cutOrderedPhysicalTimes_relativeFinalSegment
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_splitFinitePath

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pulling a finite-time concatenation back to mixed labels

This file records the reindexing step after an ordered finite-dimensional law has been split at
a designated cut.  A mixed label may select a past coordinate, a strict-future coordinate, or
the terminal past coordinate.  The last alternative permits a future-zero label to duplicate a
terminal past label without requiring either label to be present.

The result is pure finite-dimensional Chapman--Kolmogorov algebra.  In particular it has no
continuity, density, path-space, or Feller hypothesis.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]



/-- Pullback to mixed labels is measurable, including when either label type is empty and when
several labels select the terminal coordinate. -/
theorem measurable_pullbackSplitFinitePath {m n : ℕ}
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n)) :
    Measurable
      (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex) := by
  rw [measurable_pi_iff]
  rintro (i | j)
  · exact (measurable_pi_apply (pastIndex i)).comp measurable_fst
  · cases h : futureIndex j with
    | none =>
        simpa only [pullbackSplitFinitePath, h] using!
          ((measurable_pi_apply (Fin.last m)).comp measurable_fst)
    | some k =>
        simpa only [pullbackSplitFinitePath, h] using!
          ((measurable_pi_apply k).comp measurable_snd)

namespace IsConservative

/-- Concatenation at an ordered cut remains valid after pulling the two pieces back to arbitrary
mixed labels.  Mapping a future label to `none` reads the cut coordinate from the past, so the
theorem directly permits simultaneous terminal-past/future-zero observations. -/
theorem finiteTimeKernel_map_pullbackSplitFinitePath
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (m n : ℕ) (times : FiniteOrderedTimes (n + (m + 1)))
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n)) :
    (finiteTimeKernel P times).map
        (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex ∘
          splitFinitePath (alpha := alpha) (m := m) (n := n)) =
      (finiteTimeKernel P (FiniteOrderedTimes.initialSegment times) ⊗ₖ
        (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times)).comap
          (splitPastTerminal (alpha := alpha) (m := m))
          measurable_splitPastTerminal).map
        (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex) := by
  rw [Kernel.map_comp_right]
  · rw [hP.finiteTimeKernel_map_splitFinitePath P m n times]
  · exact measurable_splitFinitePath
  · exact measurable_pullbackSplitFinitePath pastIndex futureIndex

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/

namespace MarkovProcess

section MixedPastFutureCoordinates

open MeasureTheory


noncomputable section

namespace MixedPastFuture



































variable {alpha : Type*} [MeasurableSpace alpha]



end MixedPastFuture

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]











variable [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



end ContinuousPath
end

end MixedPastFutureCoordinates

section MixedPastFutureCutCoordinates

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MixedPastFuture

noncomputable section











































































variable {alpha : Type*}





variable [MeasurableSpace alpha]



















end
end MixedPastFuture

namespace SubMarkovKernelSemigroup
namespace IsConservative





end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutCoordinates

section MixedPastFutureCutFactorization

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace SubMarkovKernelSemigroup
namespace IsConservative



end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutFactorization

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
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/




open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory





namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (pastIndex : pastLabel → Fin (MixedPastFuture.pastPredecessorCard S I + 1))
    (futureIndex : futureLabel →
      Option (Fin (MixedPastFuture.positiveFutureFinset S I).card)) :
    (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
      (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
        (MarkovProcess.SubMarkovKernelSemigroup.pullbackSplitFinitePath
          (alpha := alpha) pastIndex futureIndex ∘
          MarkovProcess.SubMarkovKernelSemigroup.splitFinitePath
            (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I)
            (n := (MixedPastFuture.positiveFutureFinset S I).card)) =
      (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.cutPastOrderedPhysicalTimes S I) ⊗ₖ
        (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (MarkovProcess.SubMarkovKernelSemigroup.splitPastTerminal
              (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            MarkovProcess.SubMarkovKernelSemigroup.measurable_splitPastTerminal).map
        (MarkovProcess.SubMarkovKernelSemigroup.pullbackSplitFinitePath
          (alpha := alpha) pastIndex futureIndex) := by
  rw [← MixedPastFuture.cutOrderedPhysicalTimes_initialSegment S I,
    ← MixedPastFuture.cutOrderedPhysicalTimes_relativeFinalSegment S I]
  exact hP.finiteTimeKernel_map_pullbackSplitFinitePath P
    (MixedPastFuture.pastPredecessorCard S I)
    (MixedPastFuture.positiveFutureFinset S I).card
    (MixedPastFuture.cutOrderedPhysicalTimes S I) pastIndex futureIndex
