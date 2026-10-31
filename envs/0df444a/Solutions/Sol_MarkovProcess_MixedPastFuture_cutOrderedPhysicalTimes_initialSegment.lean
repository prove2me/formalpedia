-- Prove2me | solution 1 for MarkovProcess.MixedPastFuture.cutOrderedPhysicalTimes_initialSegment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:56:10.271904+00:00
-- url     : https://prove2.me/submissions/c4c6eedb-c581-423a-bbf2-947ed7136e0a

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

private theorem sort_union_eq_append {beta : Type*} [LinearOrder beta]
    (A B : Finset beta) (hAB : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (A ∪ B).sort = A.sort ++ B.sort := by
  apply (A ∪ B).sortedLT_sort.eq_of_mem_iff
  · rw [List.sortedLT_iff_pairwise, List.pairwise_append]
    exact ⟨A.sortedLT_sort.pairwise, B.sortedLT_sort.pairwise, fun a ha b hb ↦
      hAB a ((A.mem_sort (· ≤ ·)).mp ha) b ((B.mem_sort (· ≤ ·)).mp hb)⟩
  · intro x
    simp only [Finset.mem_sort, Finset.mem_union, List.mem_append]









































































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
    FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) =
      cutPastOrderedPhysicalTimes S I := by
  apply DFunLike.ext _ _
  intro i
  change
    (absolutePhysicalFinsetWithTerminal S I).orderEmbOfFin
      (card_absolutePhysicalFinsetWithTerminal S I)
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.castAdd (positiveFutureFinset S I).card i)) =
      (pastPhysicalFinsetWithTerminal S I).orderEmbOfFin
        (by rw [pastPhysicalFinsetWithTerminal,
          SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
          card_pastWithTerminalFinset]) i
  have hsort : (absolutePhysicalFinsetWithTerminal S I).sort =
      (pastPhysicalFinsetWithTerminal S I).sort ++
        (positiveFutureAbsolutePhysicalFinset S I).sort := by
    rw [absolutePhysicalFinsetWithTerminal_eq_union]
    exact sort_union_eq_append _ _
      (pastPhysical_lt_positiveFutureAbsolutePhysical S I)
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [hsort]
  have hcardPast : (pastPhysicalFinsetWithTerminal S I).card = pastPredecessorCard S I + 1 := by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  have hb : i.val < (pastPhysicalFinsetWithTerminal S I).sort.length := by
    rw [Finset.length_sort, hcardPast]
    exact i.isLt
  exact List.getElem_append_left hb
