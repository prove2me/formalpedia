-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_restrictPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:16:36.409824+00:00
-- url     : https://prove2.me/submissions/773ed30b-112f-47a3-bd39-442276b297f3

import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_removeNth
import Theorems.Thm_MarkovProcess_exists_factor_succAboveOrderEmb
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
# Deleting one coordinate from a finite-time kernel

For a conservative sub-Markov kernel semigroup, removing one observation from a finite-time law
gives the law on the remaining ordered times.  This is finite-dimensional kernel infrastructure;
it does not construct a path-space law or a stochastic process.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]













namespace IsConservative



/-- The deletion theorem in the common path-restriction notation. -/
theorem finiteTimeKernel_map_restrictPath_succAbove (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (p : Fin (n + 1)) :
    (finiteTimeKernel P times).map
        (FiniteOrderedTimes.restrictPath (Fin.succAboveOrderEmb p)) =
      finiteTimeKernel P (times.restrict (Fin.succAboveOrderEmb p)) :=
  hP.finiteTimeKernel_map_removeNth P times p
end IsConservative
end SubMarkovKernelSemigroup
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





















/-- Restriction along the identity order embedding does not change the time family. -/
@[simp]
theorem restrict_id {n : ℕ} (times : FiniteOrderedTimes n) :
    times.restrict (OrderIso.refl (Fin n)).toOrderEmbedding = times :=
  rfl

/-- Successive restrictions agree with restriction along the composite embedding. -/
@[simp]
theorem restrict_trans {k m n : ℕ} (times : FiniteOrderedTimes n)
    (e : Fin m ↪o Fin n) (d : Fin k ↪o Fin m) :
    (times.restrict e).restrict d = times.restrict (d.trans e) :=
  rfl





/-- Path restriction along the identity embedding is the identity. -/
@[simp]
theorem restrictPath_id {n : ℕ} {α : Type*} (path : Fin n → α) :
    restrictPath (OrderIso.refl (Fin n)).toOrderEmbedding path = path :=
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
# Restricting finite-time kernels

For a conservative sub-Markov kernel semigroup, restriction along any finite order embedding
gives the finite-time kernel at the selected times. This is finite-dimensional kernel
infrastructure and does not construct a path-space law or a stochastic process.
-/

open ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

private theorem fin_orderEmbedding_self_eq_id {n : ℕ} (e : Fin n ↪o Fin n) :
    e = (OrderIso.refl (Fin n)).toOrderEmbedding := by
  let eo : Fin n ≃o Fin n :=
    { Equiv.ofBijective e ⟨e.injective, Finite.surjective_of_injective e.injective⟩ with
      map_rel_iff' := e.le_iff_le }
  apply DFunLike.ext _ _
  intro i
  apply Fin.ext
  exact Fin.coe_orderIso_apply eo i



theorem solution
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n) :
    (finiteTimeKernel P times).map (FiniteOrderedTimes.restrictPath e) =
      finiteTimeKernel P (times.restrict e) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by
        have hcard := Fintype.card_le_of_injective e e.injective
        simpa only [Fintype.card_fin, Nat.le_zero] using hcard
      subst m
      rw [fin_orderEmbedding_self_eq_id e]
      rw [show (FiniteOrderedTimes.restrictPath (OrderIso.refl (Fin 0)).toOrderEmbedding :
            (Fin 0 → α) → Fin 0 → α) = id by
          funext path
          exact FiniteOrderedTimes.restrictPath_id path]
      rw [Kernel.map_id, FiniteOrderedTimes.restrict_id]
  | succ n ih =>
      have hcard : m ≤ n + 1 := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
      by_cases hm : m = n + 1
      · subst m
        rw [fin_orderEmbedding_self_eq_id e]
        rw [show (FiniteOrderedTimes.restrictPath
              (OrderIso.refl (Fin (n + 1))).toOrderEmbedding :
              (Fin (n + 1) → α) → Fin (n + 1) → α) = id by
            funext path
            exact FiniteOrderedTimes.restrictPath_id path]
        rw [Kernel.map_id, FiniteOrderedTimes.restrict_id]
      · have hmn : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hcard hm)
        obtain ⟨p, d, hd⟩ := exists_factor_succAboveOrderEmb e hmn
        rw [← hd]
        have hdelete := hP.finiteTimeKernel_map_restrictPath_succAbove P times p
        have hdel : Measurable (FiniteOrderedTimes.restrictPath
            (Fin.succAboveOrderEmb p) : (Fin (n + 1) → α) → Fin n → α) :=
          FiniteOrderedTimes.measurable_restrictPath (Fin.succAboveOrderEmb p)
        have hdmeas : Measurable
            (FiniteOrderedTimes.restrictPath d : (Fin n → α) → Fin m → α) :=
          FiniteOrderedTimes.measurable_restrictPath d
        rw [show (FiniteOrderedTimes.restrictPath (d.trans (Fin.succAboveOrderEmb p)) :
              (Fin (n + 1) → α) → Fin m → α) =
            FiniteOrderedTimes.restrictPath d ∘
              FiniteOrderedTimes.restrictPath (Fin.succAboveOrderEmb p) by rfl]
        rw [Kernel.map_comp_right _ hdel hdmeas, hdelete,
          ih (times.restrict (Fin.succAboveOrderEmb p)) d,
          FiniteOrderedTimes.restrict_trans]
