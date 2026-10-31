-- Prove2me | solution 1 for MarkovProcess.MixedPastFuture.cutOrderedPhysicalTimes_relativeFinalSegment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:25.364027+00:00
-- url     : https://prove2.me/submissions/03ef0263-6fa6-4b64-99f3-f8319442e6d0

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
import Theorems.Thm_MarkovProcess_MixedPastFuture_cutPastOrderedPhysicalTimes_last

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
open MarkovProcess.MixedPastFuture
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























































namespace MarkovProcess.MixedPastFuture

end MarkovProcess.MixedPastFuture
open MarkovProcess.MixedPastFuture
theorem solution (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes.relativeFinalSegment
        (cutOrderedPhysicalTimes S I) =
      positiveFutureOrderedPhysicalTimes S I := by
  let F := SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)
  have hcard : F.card = (positiveFutureFinset S I).card := by
    simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map]
  change FiniteOrderedTimes.relativeFinalSegment
      (cutOrderedPhysicalTimes S I) = F.orderEmbOfFin hcard
  apply Finset.orderEmbOfFin_unique' hcard
  intro i
  have hcut : cutOrderedPhysicalTimes S I
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.castAdd (positiveFutureFinset S I).card
          (Fin.last (pastPredecessorCard S I)))) =
      DenseTime.castOrderEmbedding S := by
    change FiniteOrderedTimes.initialSegment
      (cutOrderedPhysicalTimes S I) (Fin.last (pastPredecessorCard S I)) = _
    rw [cutOrderedPhysicalTimes_initialSegment, cutPastOrderedPhysicalTimes_last]
  have hfut := cutOrderedPhysicalTimes_future_mem S I i
  rw [positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at hfut
  obtain ⟨u, hu, hu_eq⟩ := hfut
  obtain ⟨t, ht, hut⟩ :=
    (DenseTime.mem_addFinset S (positiveFutureFinset S I) u).mp hu
  subst u
  simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
  refine ⟨t, ht, ?_⟩
  rw [FiniteOrderedTimes.relativeFinalSegment_apply,
    hcut, ← hu_eq]
  change DenseTime.castOrderEmbedding t =
    DenseTime.castOrderEmbedding (S + t) - DenseTime.castOrderEmbedding S
  rw [DenseTime.castOrderEmbedding_add, add_tsub_cancel_left]
