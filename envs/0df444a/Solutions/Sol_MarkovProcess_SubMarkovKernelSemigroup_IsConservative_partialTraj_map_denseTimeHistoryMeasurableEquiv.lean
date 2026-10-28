-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.partialTraj_map_denseTimeHistoryMeasurableEquiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:36:51.578231+00:00
-- url     : https://prove2.me/submissions/2e55b20a-1928-4edd-a0ea-b767fd84531f

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
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
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_augmentedPrefixKernel_step
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

@[simp]
theorem splitLast_snd (n : ℕ) (path : Fin (n + 1) → α) :
    (splitLast n path).2 = path (Fin.last n) :=
  rfl

@[simp]
theorem splitLast_symm_apply_castSucc (n : ℕ) (path : Fin n → α) (x : α) (i : Fin n) :
    (splitLast n).symm (path, x) i.castSucc = path i := by
  have h := splitLast_fst_apply n ((splitLast n).symm (path, x)) i
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem splitLast_symm_apply_last (n : ℕ) (path : Fin n → α) (x : α) :
    (splitLast n).symm (path, x) (Fin.last n) = x := by
  have h := splitLast_snd n ((splitLast n).symm (path, x))
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm
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

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]







namespace IsConservative

variable [StandardBorelSpace α] [Nonempty α]

omit [StandardBorelSpace α] [Nonempty α] in
/-- Augmented finite-history laws are Markov kernels under conservativity. -/
theorem isMarkovKernel_augmentedPrefixKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (augmentedPrefixKernel P e ι n) := by
  rw [augmentedPrefixKernel, Kernel.mapOfMeasurable_eq_map]
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.historyEquiv n).symm.measurable
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





end ProbabilityTheory.Kernel

namespace MarkovProcess
namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]



/-- Adjoining one observation to a finite dense-time history is measurable. -/
theorem measurable_append (n : ℕ) : Measurable (append (α := α) n) := by
  unfold append
  fun_prop

@[simp]
theorem historyEquiv_append (n : ℕ) (history : DenseTimeHistory α n) (x : α) :
    historyEquiv (n + 1) (append n (history, x)) =
      ((historyEquiv n history).1, (splitLast n).symm ((historyEquiv n history).2, x)) := by
  exact MeasurableEquiv.apply_symm_apply _ _

@[simp]
theorem append_apply_castSucc (n : ℕ) (history : DenseTimeHistory α n) (x : α)
    (i : Set.Iic n) :
    append n (history, x) ⟨i, i.property.trans n.le_succ⟩ = history i := by
  rcases i with ⟨_ | i, hi⟩
  · change (historyEquiv (n + 1) (append n (history, x))).1 =
      (historyEquiv n history).1
    rw [historyEquiv_append]
  · let j : Fin n := ⟨i, Nat.succ_le_iff.mp hi⟩
    change (historyEquiv (n + 1) (append n (history, x))).2 j.castSucc =
      (historyEquiv n history).2 j
    rw [historyEquiv_append]
    change (splitLast n).symm ((historyEquiv n history).2, x) j.castSucc = _
    rw [splitLast_symm_apply_castSucc]

@[simp]
theorem append_apply_last (n : ℕ) (history : DenseTimeHistory α n) (x : α) :
    append n (history, x) ⟨n + 1, Nat.le_refl (n + 1)⟩ = x := by
  change (historyEquiv (n + 1) (append n (history, x))).2 (Fin.last n) = x
  rw [historyEquiv_append]
  change (splitLast n).symm ((historyEquiv n history).2, x) (Fin.last n) = x
  rw [splitLast_symm_apply_last]
end DenseTimeHistory
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/

open MeasureTheory ProbabilityTheory


noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]



























private def rawTrajAppend (n : ℕ) :
    ((↑(Finset.Iic n) → α) × α) → (↑(Finset.Iic (n + 1)) → α) :=
  IicProdIoc (X := fun _ ↦ α) n (n + 1) ∘
    Prod.map id (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n)

omit [StandardBorelSpace α] [Nonempty α] in
private theorem denseTimeHistoryMeasurableEquiv_rawTrajAppend (n : ℕ) :
    denseTimeHistoryMeasurableEquiv (α := α) (n + 1) ∘ rawTrajAppend n =
      DenseTimeHistory.append n ∘
        Prod.map (denseTimeHistoryMeasurableEquiv (α := α) n) id := by
  funext z
  funext i
  rcases i with ⟨i, hi⟩
  dsimp only [Function.comp_apply, Prod.map_apply, id_eq]
  change rawTrajAppend n z ⟨i, Finset.mem_Iic.mpr hi⟩ =
    DenseTimeHistory.append n (denseTimeHistoryMeasurableEquiv n z.1, z.2) ⟨i, hi⟩
  by_cases hiz : i = 0
  · subst i
    rfl
  · by_cases hin : i = n + 1
    · subst i
      change (if h : n + 1 ≤ n then
        z.1 ⟨n + 1, Finset.mem_Iic.mpr h⟩ else z.2) = _
      rw [DenseTimeHistory.append_apply_last]
      simp only [Nat.not_succ_le_self, dite_false]
    · have hi' : i ≤ n + 1 := hi
      have hil : i ≤ n := by omega
      let j : Set.Iic n := ⟨i, hil⟩
      simp only [rawTrajAppend, Function.comp_apply, IicProdIoc_def,
        MeasurableEquiv.piSingleton]
      rw [dif_pos hil]
      rw [DenseTimeHistory.append_apply_castSucc n
        (denseTimeHistoryMeasurableEquiv n z.1) z.2 j]
      rfl

private theorem transport_traj_step {X H Z Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace T]
    (κ : Kernel X Z) [IsSFiniteKernel κ]
    (η : Kernel Z Y) [IsSFiniteKernel η] (E : H ≃ᵐ Z)
    (g : H × Y → T) (hg : Measurable g) (q : Z × Y → T)
    (hcompat : g ∘ Prod.map E.symm id = q) :
    (((Kernel.id ×ₖ η.comap E E.measurable) ∘ₖ κ.map E.symm).map g) =
      ((Kernel.id ×ₖ η) ∘ₖ κ).map q := by
  rw [Kernel.comp_map κ (Kernel.id ×ₖ η.comap E E.measurable) E.symm.measurable]
  rw [Kernel.comap_prod, Kernel.id_comap, ← Kernel.id_map,
    ← Kernel.comap_comp_right]
  have hcomap : η.comap ((E : H → Z) ∘ E.symm)
      (E.measurable.comp E.symm.measurable) = η := by
    ext z
    rw [Kernel.comap_apply]
    change η (E (E.symm z)) _ = η z _
    rw [E.apply_symm_apply]
  rw [hcomap, ← Kernel.map_id' η, Kernel.map_prod_map,
    ← Kernel.map_comp, ← Kernel.map_comp_right, Kernel.map_id']
  change (Kernel.id ×ₖ η ∘ₖ κ).map (g ∘ Prod.map E.symm id) = _
  rw [hcompat]
  all_goals first | exact hg | fun_prop

omit [StandardBorelSpace α] [Nonempty α] in
private theorem markovKernel_finZero (κ : Kernel α (Fin 0 → α)) [IsMarkovKernel κ] :
    κ = Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α)) := by
  ext x s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp
  · have hsu : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y z] using hz
    rw [hsu]
    simp only [Kernel.const_apply, IsProbabilityMeasure.measure_univ]


theorem solution
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    ((Kernel.partialTraj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0 n ∘ₖ
      initialTrajHistoryKernel).map (denseTimeHistoryMeasurableEquiv n)) =
      augmentedPrefixKernel P e ι n := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_comp]
      let : IsMarkovKernel (denseTimePrefixKernel P e ι 0) :=
        hP.isMarkovKernel_denseTimePrefixKernel P e ι 0
      rw [augmentedPrefixKernel,
        markovKernel_finZero (denseTimePrefixKernel P e ι 0)]
      have hconst : Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α)) =
          Kernel.deterministic (fun _ : α ↦ FiniteOrderedTimes.emptyPath α)
            measurable_const := by
        ext x s hs
        simp only [Kernel.const_apply, Kernel.deterministic_apply,
          Measure.dirac_apply' _ hs]
      rw [initialTrajHistoryKernel, Kernel.deterministic_map, hconst, Kernel.id,
        Kernel.deterministic_prod_deterministic, Kernel.mapOfMeasurable_eq_map,
        Kernel.deterministic_map]
      apply Kernel.deterministic_congr
      funext x i
      rcases i with ⟨i, hi⟩
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      rfl
      all_goals fun_prop
  | succ n ih =>
      let : IsMarkovKernel (denseStep P hP e ι n) :=
        isMarkovKernel_denseStep P hP e ι n
      let : IsMarkovKernel (augmentedPrefixKernel P e ι n) :=
        isMarkovKernel_augmentedPrefixKernel P hP e ι n
      rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n)]
      rw [← Kernel.map_comp]
      rw [Kernel.comp_assoc]
      rw [← Kernel.map_comp_right]
      · rw [← Kernel.map_id' Kernel.id, Kernel.map_prod_map] <;> try fun_prop
        rw [← Kernel.map_comp]
        rw [← Kernel.map_comp_right]
        · have hfun :
              ((denseTimeHistoryMeasurableEquiv (α := α) (n + 1) :
                  (↑(Finset.Iic (n + 1)) → α) → DenseTimeHistory α (n + 1)) ∘
                IicProdIoc (X := fun _ ↦ α) n (n + 1)) ∘
                  Prod.map (fun a ↦ a)
                    (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n) =
                denseTimeHistoryMeasurableEquiv (n + 1) ∘ rawTrajAppend n := by
              rfl
          rw [hfun, denseTimeHistoryMeasurableEquiv_rawTrajAppend]
          have hkraw :=
            (Kernel.map_apply_eq_iff_map_symm_apply_eq
              (Kernel.partialTraj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0 n ∘ₖ
                initialTrajHistoryKernel)
              (augmentedPrefixKernel P e ι n)).mp ih
          rw [hkraw, trajDenseStep, transport_traj_step, augmentedPrefixKernel_step]
          · exact (DenseTimeHistory.measurable_append n).comp
              ((denseTimeHistoryMeasurableEquiv n).measurable.prodMap measurable_id)
          · funext z
            change DenseTimeHistory.append n
              ((denseTimeHistoryMeasurableEquiv n)
                ((denseTimeHistoryMeasurableEquiv n).symm z.1), z.2) =
              DenseTimeHistory.append n z
            rw [MeasurableEquiv.apply_symm_apply]
        · exact measurable_id.prodMap
            (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n).measurable
        · exact (denseTimeHistoryMeasurableEquiv (α := α) (n + 1)).measurable.comp
            measurable_IicProdIoc
      · exact measurable_IicProdIoc
      · exact (denseTimeHistoryMeasurableEquiv (α := α) (n + 1)).measurable
