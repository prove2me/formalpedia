-- Prove2me | solution 1 for MarkovProcess.edist_unitDyadicGrid_child_parent_le_of_adjacent_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:13:51.252045+00:00
-- url     : https://prove2.me/submissions/04298421-b292-4a6b-a233-743bd5706d63

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/



open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]



@[simp]
theorem MarkovProcess.unitDyadicRefineIndex_val (n : ℕ) (i : Fin (2 ^ n + 1)) :
    (unitDyadicRefineIndex n i).val = 2 * i.val :=
  rfl

/-- Refinement does not change the represented nonnegative rational time. -/
theorem MarkovProcess.unitDyadicGrid_refineIndex (n : ℕ) (i : Fin (2 ^ n + 1)) :
    unitDyadicGrid (n + 1) (unitDyadicRefineIndex n i) = unitDyadicGrid n i := by
  simp only [unitDyadicGrid, unitDyadicRefineIndex_val]
  rw [pow_succ]
  push_cast
  field_simp



@[simp]
theorem MarkovProcess.unitDyadicParentIndex_val (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    (unitDyadicParentIndex n i).val = i.val / 2 :=
  rfl

/-- Refining the parent lies weakly to the left of its child. -/
theorem MarkovProcess.unitDyadicRefineIndex_parent_le (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    (unitDyadicRefineIndex n (unitDyadicParentIndex n i)).val ≤ i.val := by
  simp only [unitDyadicRefineIndex_val, unitDyadicParentIndex_val]
  omega

/-- A child is at most one fine-grid cell to the right of its refined parent. -/
theorem MarkovProcess.unitDyadic_child_sub_refineIndex_parent_le_one
    (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    i.val - (unitDyadicRefineIndex n (unitDyadicParentIndex n i)).val ≤ 1 := by
  simp only [unitDyadicRefineIndex_val, unitDyadicParentIndex_val]
  omega

/-- The coarse-grid parent represents the same time as its refinement on the fine grid. -/
theorem MarkovProcess.unitDyadicGrid_parent_eq_refineIndex
    (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    unitDyadicGrid n (unitDyadicParentIndex n i) =
      unitDyadicGrid (n + 1) (unitDyadicRefineIndex n (unitDyadicParentIndex n i)) := by
  exact (unitDyadicGrid_refineIndex n (unitDyadicParentIndex n i)).symm


theorem solution
    {X : NNRat → Ω → E} {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ (n + 1)),
      edist (X (unitDyadicGrid (n + 1) k.castSucc) ω)
          (X (unitDyadicGrid (n + 1) k.succ) ω) ≤ ε)
    (i : Fin (2 ^ (n + 1) + 1)) :
    edist (X (unitDyadicGrid (n + 1) i) ω)
        (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) ≤ ε := by
  let j := unitDyadicRefineIndex n (unitDyadicParentIndex n i)
  have hji : j.val ≤ i.val := unitDyadicRefineIndex_parent_le n i
  have hsub : i.val - j.val ≤ 1 :=
    unitDyadic_child_sub_refineIndex_parent_le_one n i
  calc
    edist (X (unitDyadicGrid (n + 1) i) ω)
        (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) =
        edist (X (unitDyadicGrid (n + 1) j) ω)
          (X (unitDyadicGrid (n + 1) i) ω) := by
      rw [edist_comm, unitDyadicGrid_parent_eq_refineIndex]
    _ ≤ (i.val - j.val : ℕ) * ε :=
      edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le hadj j i hji
    _ ≤ (1 : ℝ≥0∞) * ε := by
      have hcast : ((i.val - j.val : ℕ) : ℝ≥0∞) ≤ 1 := by exact_mod_cast hsub
      exact mul_le_mul_of_nonneg_right hcast bot_le
    _ = ε := one_mul ε
