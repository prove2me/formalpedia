-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_removeNth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:08:48.486979+00:00
-- url     : https://prove2.me/submissions/95e0dba9-232f-473d-84b0-081f12141e26

import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_translate
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
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess



namespace FiniteOrderedTimes



@[simp]
theorem relativeTail_apply {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (i : Fin n) :
    times.relativeTail i = times i.succ - times 0 :=
  rfl



@[simp]
theorem translate_apply {n : ℕ} (s : NNReal) (times : FiniteOrderedTimes n) (i : Fin n) :
    times.translate s i = s + times i :=
  rfl

/-- The original successor time is the first time plus its relative-tail coordinate. -/
theorem add_relativeTail {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (i : Fin n) :
    times 0 + times.relativeTail i = times i.succ :=
  add_tsub_cancel_of_le (times.monotone (Fin.zero_le _))









@[simp]
theorem restrict_apply {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n)
    (i : Fin m) : times.restrict e i = times (e i) :=
  rfl













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
# Deleting one coordinate from a finite-time kernel

For a conservative sub-Markov kernel semigroup, removing one observation from a finite-time law
gives the law on the remaining ordered times.  This is finite-dimensional kernel infrastructure;
it does not construct a path-space law or a stochastic process.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

private theorem measurable_removeNth {n : ℕ} (p : Fin (n + 1)) :
    Measurable (Fin.removeNth p : (Fin (n + 1) → α) → Fin n → α) :=
  FiniteOrderedTimes.measurable_restrictPath (Fin.succAboveOrderEmb p)

private theorem map_compProd_prodMkLeft_right
    {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W]
    (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : Z → W) (hf : Measurable f) :
    (κ ⊗ₖ Kernel.prodMkLeft X η).map (fun z ↦ (z.1, f z.2)) =
      κ ⊗ₖ Kernel.prodMkLeft X (η.map f) := by
  have hpair : Measurable (fun z : Y × Z ↦ (z.1, f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs,
    Kernel.compProd_apply (hs.preimage hpair), Kernel.compProd_apply hs]
  congr with y
  have hsection : MeasurableSet (Prod.mk y ⁻¹' s) := measurable_prodMk_left hs
  rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply',
    Kernel.map_apply' _ hf _ hsection]
  rfl

omit [MeasurableSpace α] in
private theorem removeNth_zero_cons {n : ℕ} (z : α × (Fin n → α)) :
    Fin.removeNth 0 (@Fin.cons n (fun _ ↦ α) z.1 z.2) = z.2 := by
  ext i
  rfl

omit [MeasurableSpace α] in
private theorem removeNth_succ_cons {n : ℕ} (p : Fin (n + 1))
    (z : α × (Fin (n + 1) → α)) :
    Fin.removeNth p.succ (@Fin.cons (n + 1) (fun _ ↦ α) z.1 z.2) =
      @Fin.cons n (fun _ ↦ α) z.1 (Fin.removeNth p z.2) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · simp only [Fin.removeNth_apply, Fin.cons_succ]
    rw [Fin.succ_succAbove_succ]
    rfl

private theorem translate_relativeTail_eq_restrict_zero {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) :
    times.relativeTail.translate (times 0) =
      times.restrict (Fin.succAboveOrderEmb 0) := by
  apply DFunLike.ext _ _
  intro i
  rw [FiniteOrderedTimes.translate_apply, FiniteOrderedTimes.restrict_apply,
    Fin.succAboveOrderEmb_apply, Fin.succAbove_zero_apply]
  exact FiniteOrderedTimes.add_relativeTail times i

private theorem relativeTail_restrict_succ {n : ℕ} (times : FiniteOrderedTimes (n + 2))
    (p : Fin (n + 1)) :
    (times.restrict (Fin.succAboveOrderEmb p.succ)).relativeTail =
      times.relativeTail.restrict (Fin.succAboveOrderEmb p) := by
  apply DFunLike.ext _ _
  intro i
  simp only [FiniteOrderedTimes.relativeTail_apply, FiniteOrderedTimes.restrict_apply,
    Fin.succAboveOrderEmb_apply]
  rw [Fin.succ_succAbove_succ, Fin.succ_succAbove_zero]



theorem solution (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (p : Fin (n + 1)) :
    (finiteTimeKernel P times).map (Fin.removeNth p) =
      finiteTimeKernel P (times.restrict (Fin.succAboveOrderEmb p)) := by
  induction n with
  | zero =>
      have hp : p = 0 := Fin.eq_zero p
      subst p
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
      · rw [show (Fin.removeNth 0 ∘ fun z : α × (Fin 0 → α) ↦
              @Fin.cons 0 (fun _ ↦ α) z.1 z.2) = Prod.snd by
                funext z
                exact removeNth_zero_cons z]
        rw [← Kernel.snd_eq, Kernel.snd_compProd_prodMkLeft,
          ← hP.finiteTimeKernel_translate, translate_relativeTail_eq_restrict_zero]
      · exact measurable_finCons
      · exact measurable_removeNth 0
  | succ n ih =>
      refine Fin.cases ?_ (fun p ↦ ?_) p
      · let : IsFiniteKernel (P (times 0)) :=
          (P.isSubMarkovKernel (times 0)).isFiniteKernel
        let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
          hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
        rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
        · rw [show (Fin.removeNth 0 ∘ fun z : α × (Fin (n + 1) → α) ↦
                @Fin.cons (n + 1) (fun _ ↦ α) z.1 z.2) = Prod.snd by
                  funext z
                  exact removeNth_zero_cons z]
          rw [← Kernel.snd_eq, Kernel.snd_compProd_prodMkLeft,
            ← hP.finiteTimeKernel_translate, translate_relativeTail_eq_restrict_zero]
        · exact measurable_finCons
        · exact measurable_removeNth 0
      · let : IsFiniteKernel (P (times 0)) :=
          (P.isSubMarkovKernel (times 0)).isFiniteKernel
        let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
          hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
        rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
        · rw [show (Fin.removeNth p.succ ∘ fun z : α × (Fin (n + 1) → α) ↦
              @Fin.cons (n + 1) (fun _ ↦ α) z.1 z.2) =
              (fun z : α × (Fin (n + 1) → α) ↦
                @Fin.cons n (fun _ ↦ α) z.1 (Fin.removeNth p z.2)) by
                funext z
                exact removeNth_succ_cons p z]
          rw [show (fun z : α × (Fin (n + 1) → α) ↦
                @Fin.cons n (fun _ ↦ α) z.1 (Fin.removeNth p z.2)) =
              (fun z : α × (Fin n → α) ↦
                @Fin.cons n (fun _ ↦ α) z.1 z.2) ∘
                (fun z : α × (Fin (n + 1) → α) ↦
                  (z.1, Fin.removeNth p z.2)) by rfl]
          have hremovePair : Measurable (fun z : α × (Fin (n + 1) → α) ↦
              (z.1, Fin.removeNth p z.2)) :=
            measurable_fst.prodMk ((measurable_removeNth p).comp measurable_snd)
          have hcons : Measurable (fun z : α × (Fin n → α) ↦
              @Fin.cons n (fun _ ↦ α) z.1 z.2) := measurable_finCons
          have hhead : (times.restrict (Fin.succAboveOrderEmb p.succ)) 0 = times 0 := by
            rw [FiniteOrderedTimes.restrict_apply, Fin.succAboveOrderEmb_apply,
              Fin.succ_succAbove_zero]
          rw [Kernel.map_comp_right _ hremovePair hcons,
            map_compProd_prodMkLeft_right _ _ _ (measurable_removeNth p),
            ih times.relativeTail p, finiteTimeKernel_succ,
            Kernel.mapOfMeasurable_eq_map, relativeTail_restrict_succ, hhead]
        · exact measurable_finCons
        · exact measurable_removeNth p.succ
