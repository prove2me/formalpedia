-- Prove2me | solution 1 for MarkovProcess.MixedPastFuture.cutPastOrderedPhysicalTimes_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:56:23.845098+00:00
-- url     : https://prove2.me/submissions/b4fc540d-dfde-4cbb-90ed-f8a12d0dd051

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
    cutPastOrderedPhysicalTimes S I (Fin.last (pastPredecessorCard S I)) =
      DenseTime.castOrderEmbedding S := by
  let A := pastPhysicalFinsetWithTerminal S I
  have hcard : A.card = pastPredecessorCard S I + 1 := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  change A.orderEmbOfFin hcard (Fin.last (pastPredecessorCard S I)) = _
  have hi : Fin.last (pastPredecessorCard S I) =
      ⟨pastPredecessorCard S I + 1 - 1,
        Nat.sub_lt (Nat.succ_pos _) Nat.zero_lt_one⟩ := by
    apply Fin.ext
    simp only [Fin.last, Nat.add_sub_cancel_right]
  rw [hi]
  rw [Finset.orderEmbOfFin_last hcard (Nat.succ_pos _)]
  have hS : DenseTime.castOrderEmbedding S ∈ A := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
    exact ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S), rfl⟩
  have hA : A.Nonempty := ⟨DenseTime.castOrderEmbedding S, hS⟩
  apply (Finset.max'_eq_iff (s := A) (H := hA)
    (DenseTime.castOrderEmbedding S)).mpr
  constructor
  · exact hS
  · intro a ha
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    exact DenseTime.castOrderEmbedding.monotone
      (le_terminal_of_mem_pastWithTerminalFinset S I hr)
