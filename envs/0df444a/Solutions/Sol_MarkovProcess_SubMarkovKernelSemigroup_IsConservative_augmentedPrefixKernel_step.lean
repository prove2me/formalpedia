-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.augmentedPrefixKernel_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:34:10.043541+00:00
-- url     : https://prove2.me/submissions/d06b9710-4329-4c84-8c7a-b50a603146f1

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
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
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_nextObservationJoint_fst
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional kernels for finite dense-time histories

This file augments finite prefix laws by their starting point and disintegrates the joint law of
a prefix and its next observation. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]







namespace IsConservative

variable [StandardBorelSpace α] [Nonempty α]









/-- Disintegration exactly reconstructs the next-observation joint law. -/
theorem compProd_observationCondKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    denseTimePrefixKernel P e ι n ⊗ₖ observationCondKernel P hP e ι n =
      nextObservationJoint P e ι n := by
  rw [← nextObservationJoint_fst P hP e ι n]
  rw [observationCondKernel]
  exact Kernel.disintegrate _ _
end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-step recursion for finite dense-time histories

This file identifies the result of adjoining one conditionally sampled observation to an
augmented finite history. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

private theorem step_transport {X H Z Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace T]
    (κ : Kernel X Z) [IsSFiniteKernel κ]
    (η : Kernel Z Y) [IsSFiniteKernel η] (E : H ≃ᵐ Z)
    (g : H × Y → T) (hg : Measurable g) (q : Z × Y → T)
    (hcompat : g ∘ Prod.map E.symm id = q) :
    (((Kernel.id ×ₖ η.comap E E.measurable) ∘ₖ κ.map E.symm).map g) =
      ((Kernel.id ×ₖ η) ∘ₖ κ).map q := by
  rw [Kernel.comp_map κ (Kernel.id ×ₖ η.comap E E.measurable) E.symm.measurable]
  rw [Kernel.comap_prod]
  rw [Kernel.id_comap]
  rw [← Kernel.id_map]
  rw [← Kernel.comap_comp_right]
  have hcomap : η.comap ((E : H → Z) ∘ E.symm)
      (E.measurable.comp E.symm.measurable) = η := by
    ext z
    rw [Kernel.comap_apply]
    change η (E (E.symm z)) _ = η z _
    rw [E.apply_symm_apply]
  rw [hcomap]
  rw [← Kernel.map_id' η]
  rw [Kernel.map_prod_map]
  rw [← Kernel.map_comp]
  rw [← Kernel.map_comp_right]
  rw [Kernel.map_id']
  change (Kernel.id ×ₖ η ∘ₖ κ).map (g ∘ Prod.map E.symm id) = _
  rw [hcompat]
  all_goals first | exact hg | fun_prop

private theorem prod_comp_prod_map_prodAssoc {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel (X × A) B) [IsSFiniteKernel η] :
    (((Kernel.id ×ₖ η) ∘ₖ (Kernel.id ×ₖ κ)).map MeasurableEquiv.prodAssoc) =
      Kernel.id ×ₖ (κ ⊗ₖ η) := by
  ext x s hs
  rw [Kernel.map_apply' _ MeasurableEquiv.prodAssoc.measurable _ hs, Kernel.comp_apply]
  rw [← Measure.compProd_eq_comp_prod]
  have hfirst : (Kernel.id ×ₖ κ) x = Measure.dirac x ⊗ₘ κ := by
    rw [Measure.compProd_eq_comp_prod]
    exact (Measure.dirac_bind (Kernel.measurable (Kernel.id ×ₖ κ)) x).symm
  rw [hfirst]
  rw [← Measure.map_apply MeasurableEquiv.prodAssoc.measurable hs]
  rw [Measure.compProd_assoc']
  have hlast : (Kernel.id ×ₖ (κ ⊗ₖ η)) x = Measure.dirac x ⊗ₘ (κ ⊗ₖ η) := by
    rw [Measure.compProd_eq_comp_prod]
    exact (Measure.dirac_bind (Kernel.measurable (Kernel.id ×ₖ (κ ⊗ₖ η))) x).symm
  rw [hlast]

end ProbabilityTheory.Kernel

namespace MarkovProcess
namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]



/-- Adjoining one observation to a finite dense-time history is measurable. -/
theorem measurable_append (n : ℕ) : Measurable (append (α := α) n) := by
  unfold append
  fun_prop
end DenseTimeHistory
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-step recursion for finite dense-time histories

This file identifies the result of adjoining one conditionally sampled observation to an
augmented finite history. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory








variable {α : Type*} [MeasurableSpace α]













noncomputable section

variable {D α : Type*} [MeasurableSpace α]


variable [StandardBorelSpace α] [Nonempty α]


theorem solution (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (((Kernel.id ×ₖ denseStep P hP e ι n) ∘ₖ augmentedPrefixKernel P e ι n).map
        (DenseTimeHistory.append n)) =
      augmentedPrefixKernel P e ι (n + 1) := by
  let q : ((α × (Fin n → α)) × α) → DenseTimeHistory α (n + 1) :=
    fun z ↦ (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1.1, (DenseTimeHistory.splitLast n).symm (z.1.2, z.2))
  let r : (α × ((Fin n → α) × α)) → DenseTimeHistory α (n + 1) :=
    fun z ↦ (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1, (DenseTimeHistory.splitLast n).symm z.2)
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  let : IsMarkovKernel (denseTimePrefixKernel P e ι (n + 1)) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι (n + 1)
  let : IsMarkovKernel (observationCondKernel P hP e ι n) :=
    isMarkovKernel_observationCondKernel P hP e ι n
  have hcompat : DenseTimeHistory.append n ∘
      Prod.map (DenseTimeHistory.historyEquiv n).symm id = q := by
    funext z
    change DenseTimeHistory.append n
      ((DenseTimeHistory.historyEquiv n).symm z.1, z.2) = q z
    rw [DenseTimeHistory.append]
    change _ = (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1.1, (DenseTimeHistory.splitLast n).symm (z.1.2, z.2))
    simp only [MeasurableEquiv.apply_symm_apply]
  have htransport := Kernel.step_transport
    (Kernel.id ×ₖ denseTimePrefixKernel P e ι n)
    (observationCondKernel P hP e ι n) (DenseTimeHistory.historyEquiv n)
    (DenseTimeHistory.append n) (DenseTimeHistory.measurable_append n) q hcompat
  rw [augmentedPrefixKernel, denseStep, Kernel.mapOfMeasurable_eq_map]
  rw [htransport]
  have hq : q = r ∘ MeasurableEquiv.prodAssoc := by
    rfl
  rw [hq, Kernel.map_comp_right]
  rw [Kernel.prod_comp_prod_map_prodAssoc]
  rw [compProd_observationCondKernel P hP e ι n]
  rw [nextObservationJoint]
  rw [Kernel.mapOfMeasurable_eq_map]
  rw [← Kernel.map_id' Kernel.id]
  rw [Kernel.map_prod_map]
  rw [← Kernel.map_comp_right]
  change (Kernel.id ×ₖ denseTimePrefixKernel P e ι (n + 1)).map
    (r ∘ Prod.map id (DenseTimeHistory.splitLast n)) = _
  have hr : r ∘ Prod.map id (DenseTimeHistory.splitLast n) =
      (DenseTimeHistory.historyEquiv (n + 1)).symm := by
    funext z
    dsimp only [r, Function.comp_apply, Prod.map_apply, id_eq]
    change (DenseTimeHistory.historyEquiv (n + 1)).symm
      (z.1, (DenseTimeHistory.splitLast n).symm (DenseTimeHistory.splitLast n z.2)) = _
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hr, augmentedPrefixKernel, Kernel.mapOfMeasurable_eq_map]
  all_goals fun_prop
