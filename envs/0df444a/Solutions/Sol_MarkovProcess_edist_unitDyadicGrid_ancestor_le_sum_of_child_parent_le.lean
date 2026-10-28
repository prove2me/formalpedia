-- Prove2me | solution 1 for MarkovProcess.edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:02:02.242375+00:00
-- url     : https://prove2.me/submissions/07f6ca9a-c53b-4538-8c71-bd8ba1fb708e

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess
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























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]



@[simp]
theorem MarkovProcess.unitDyadicAncestorIndex_zero (n : ℕ) (i : Fin (2 ^ n + 1)) :
    unitDyadicAncestorIndex n 0 i = i :=
  rfl




theorem solution
    {X : NNRat → Ω → E} {n r : ℕ} {δ : ℕ → ℝ≥0∞} {ω : Ω}
    (hparent : ∀ s < r, ∀ i : Fin (2 ^ (n + s + 1) + 1),
      edist (X (unitDyadicGrid (n + s + 1) i) ω)
          (X (unitDyadicGrid (n + s) (unitDyadicParentIndex (n + s) i)) ω) ≤
        δ (n + s + 1))
    (i : Fin (2 ^ (n + r) + 1)) :
    edist (X (unitDyadicGrid (n + r) i) ω)
        (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
      ∑ s ∈ Finset.range r, δ (n + s + 1) := by
  induction r with
  | zero =>
      simp only [Nat.add_zero, unitDyadicAncestorIndex_zero, Finset.range_zero,
        Finset.sum_empty, edist_self]
      exact le_rfl
  | succ r ihr =>
      let j := unitDyadicParentIndex (n + r) i
      have hlast :
          edist (X (unitDyadicGrid (n + r + 1) i) ω)
              (X (unitDyadicGrid (n + r) j) ω) ≤ δ (n + r + 1) :=
        hparent r (Nat.lt_succ_self r) i
      have hprevious :
          edist (X (unitDyadicGrid (n + r) j) ω)
              (X (unitDyadicGrid n (unitDyadicAncestorIndex n r j)) ω) ≤
            ∑ s ∈ Finset.range r, δ (n + s + 1) := by
        apply ihr
        intro s hs k
        exact hparent s (hs.trans (Nat.lt_succ_self r)) k
      calc
        edist (X (unitDyadicGrid (n + (r + 1)) i) ω)
            (X (unitDyadicGrid n (unitDyadicAncestorIndex n (r + 1) i)) ω) =
            edist (X (unitDyadicGrid (n + r + 1) i) ω)
              (X (unitDyadicGrid n (unitDyadicAncestorIndex n r j)) ω) := by
          rfl
        _ ≤ edist (X (unitDyadicGrid (n + r + 1) i) ω)
              (X (unitDyadicGrid (n + r) j) ω) +
            edist (X (unitDyadicGrid (n + r) j) ω)
              (X (unitDyadicGrid n (unitDyadicAncestorIndex n r j)) ω) :=
          edist_triangle _ _ _
        _ ≤ δ (n + r + 1) + ∑ s ∈ Finset.range r, δ (n + s + 1) :=
          add_le_add hlast hprevious
        _ = ∑ s ∈ Finset.range (r + 1), δ (n + s + 1) := by
          rw [Finset.sum_range_succ]
          exact add_comm _ _
