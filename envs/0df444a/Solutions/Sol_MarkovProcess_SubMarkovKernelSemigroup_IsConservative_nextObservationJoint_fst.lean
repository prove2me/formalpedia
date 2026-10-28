-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.nextObservationJoint_fst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:24:40.451532+00:00
-- url     : https://prove2.me/submissions/8bdb0413-402f-44dd-94d2-40b11360d5ee

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
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
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_restrictPath
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
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/

namespace MarkovProcess

noncomputable section

namespace CountableEnumeration

variable {D : Type*}









theorem prefix_mono (e : ℕ ≃ D) : Monotone («prefix» e) := by
  intro m n hmn d
  simp only [mem_prefix_iff]
  exact fun hd ↦ hd.trans_le hmn
end CountableEnumeration
end
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess



namespace FiniteOrderedTimes

































/-- Restriction of finite coordinate paths is measurable for product measurable spaces. -/
theorem measurable_restrictPath {m n : ℕ} (e : Fin m ↪o Fin n)
    {α : Type*} [MeasurableSpace α] :
    Measurable (restrictPath e : (Fin n → α) → Fin m → α) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)
end FiniteOrderedTimes
end MarkovProcess

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

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]













private noncomputable def inclusionOrderEmb {I J : Finset NNReal} (hJI : J ⊆ I) :
    Fin J.card ↪o Fin I.card :=
  (J.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : J ↦ (⟨t, hJI t.property⟩ : I)) (fun _ _ h ↦ h)) |>.trans
    (I.orderIsoOfFin rfl).symm.toOrderEmbedding

private theorem finiteSetTimes_restrict {I J : Finset NNReal} (hJI : J ⊆ I) :
    (finiteSetTimes I).restrict (inclusionOrderEmb hJI) = finiteSetTimes J := by
  apply DFunLike.ext _ _
  intro i
  change (((I.orderIsoOfFin rfl)
      ((I.orderIsoOfFin rfl).symm
        ⟨↑(J.orderIsoOfFin rfl i), hJI (J.orderIsoOfFin rfl i).property⟩) : I) :
      NNReal) = ((J.orderIsoOfFin rfl i : J) : NNReal)
  rw [OrderIso.apply_symm_apply]

omit [MeasurableSpace α] in
private theorem orderedPathToFiniteSet_restrict {I J : Finset NNReal} (hJI : J ⊆ I) :
    Finset.restrict₂ (π := fun _ ↦ α) hJI ∘ orderedPathToFiniteSet (α := α) I =
      orderedPathToFiniteSet J ∘
        FiniteOrderedTimes.restrictPath (inclusionOrderEmb hJI) := by
  funext path t
  change path ((I.orderIsoOfFin rfl).symm ⟨t, hJI t.property⟩) =
    path (inclusionOrderEmb hJI ((J.orderIsoOfFin rfl).symm t))
  simp only [inclusionOrderEmb, RelEmbedding.coe_trans, Function.comp_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply]
  rfl

namespace IsConservative





/-- A finite-set kernel restricted along an inclusion is the kernel on the smaller set. -/
theorem finiteSetKernel_map_restrict₂ (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) {I J : Finset NNReal} (hJI : J ⊆ I) :
    finiteSetKernel P J =
      (finiteSetKernel P I).map (Finset.restrict₂ (π := fun _ ↦ α) hJI) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [orderedPathToFiniteSet_restrict hJI, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes I)
          (inclusionOrderEmb hJI), finiteSetTimes_restrict hJI]
    · exact FiniteOrderedTimes.measurable_restrictPath (inclusionOrderEmb hJI)
    · exact measurable_orderedPathToFiniteSet J
  · exact measurable_orderedPathToFiniteSet I
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ α) hJI
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

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

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]



private theorem denseTimePhysicalPrefix_mono (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    Monotone (denseTimePhysicalPrefix e ι) := by
  intro m n hmn t ht
  rw [denseTimePhysicalPrefix, Finset.mem_map] at ht ⊢
  obtain ⟨d, hd, rfl⟩ := ht
  exact ⟨d, CountableEnumeration.prefix_mono e hmn hd, rfl⟩











omit [MeasurableSpace α] in
private theorem denseTimePrefixReindex_restrict {m n : ℕ} (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (h : m ≤ n) :
    denseTimePrefixReindex (α := α) e ι m ∘
        Finset.restrict₂ (π := fun _ ↦ α) (denseTimePhysicalPrefix_mono e ι h) =
      FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h) ∘
        denseTimePrefixReindex e ι n := by
  funext path i
  rfl

namespace IsConservative





/-- Prefix kernels are exactly consistent under restriction to an earlier prefix. -/
theorem denseTimePrefixKernel_map_restrictPath (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) {m n : ℕ} (h : m ≤ n) :
    denseTimePrefixKernel P e ι m =
      (denseTimePrefixKernel P e ι n).map
        (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) := by
  rw [denseTimePrefixKernel_eq_map, denseTimePrefixKernel_eq_map,
    hP.finiteSetKernel_map_restrict₂ P (denseTimePhysicalPrefix_mono e ι h),
    ← Kernel.map_comp_right, ← Kernel.map_comp_right]
  · rw [denseTimePrefixReindex_restrict e ι h]
  · exact measurable_denseTimePrefixReindex e ι n
  · exact FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h)
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ α)
      (denseTimePhysicalPrefix_mono e ι h)
  · exact measurable_denseTimePrefixReindex e ι m
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
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/

namespace MarkovProcess



namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]



















@[simp]
theorem splitLast_fst_apply (n : ℕ) (path : Fin (n + 1) → α) (i : Fin n) :
    (splitLast n path).1 i = path i.castSucc := by
  change path ((Fin.last n).succAbove i) = path i.castSucc
  rw [Fin.succAbove_last_apply]
end DenseTimeHistory
end MarkovProcess
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


noncomputable section

variable {D α : Type*} [MeasurableSpace α]








variable [StandardBorelSpace α] [Nonempty α]



omit [StandardBorelSpace α] [Nonempty α] in

theorem solution (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (nextObservationJoint P e ι n).fst = denseTimePrefixKernel P e ι n := by
  rw [nextObservationJoint, Kernel.mapOfMeasurable_eq_map, Kernel.fst_eq,
    ← Kernel.map_comp_right]
  · change
      (denseTimePrefixKernel P e ι n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
        denseTimePrefixKernel P e ι n
    calc
      (denseTimePrefixKernel P e ι n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
          (denseTimePrefixKernel P e ι n.succ).map
            (FiniteOrderedTimes.restrictPath
              (Fin.castLEOrderEmb (Nat.le_succ n))) := by
        congr 1
        funext path i
        exact DenseTimeHistory.splitLast_fst_apply n path i
      _ = denseTimePrefixKernel P e ι n :=
        (hP.denseTimePrefixKernel_map_restrictPath P e ι (Nat.le_succ n)).symm
  · exact (DenseTimeHistory.splitLast n).measurable
  · exact measurable_fst
