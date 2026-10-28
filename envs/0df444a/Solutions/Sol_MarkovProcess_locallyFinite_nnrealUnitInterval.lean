-- Prove2me | solution 1 for MarkovProcess.locallyFinite_nnrealUnitInterval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:05:46.779647+00:00
-- url     : https://prove2.me/submissions/f8759369-bc26-4bfa-905d-9847bba7cbdf

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.LocallyFinite
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
# A global continuous modification assembled from canonical unit paths

The nonnegative real half-line is covered by the closed unit intervals `[n, n + 1]`.  On each
piece we use the canonical dyadic-floor limit of the process shifted by `n`.  Exact endpoint
identities make these pieces compatible, so `Set.liftCover` gives an honest raw global path.
On the simultaneous probability-one event where every canonical unit piece is continuous, local
finiteness of the closed cover makes the raw path continuous.  A single constant global fallback
then gives a total path which is continuous for every sample.

No measurability of the path-valued map, path-space law, Markov property, or Hunt-process claim is
asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]














theorem solution : LocallyFinite nnrealUnitInterval := by
  intro x
  let N := ⌊(x : ℝ)⌋₊ + 2
  refine ⟨Set.Iio (N : ℝ≥0), ?_, ?_⟩
  · apply Iio_mem_nhds
    have hxlt : (x : ℝ) < (N : ℕ) := by
      calc
        (x : ℝ) < ⌊(x : ℝ)⌋₊ + 1 := Nat.lt_floor_add_one (x : ℝ)
        _ < (N : ℕ) := by simp only [N]; norm_num
    exact_mod_cast hxlt
  · apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    obtain ⟨y, hy, hyN⟩ := hn
    have hny : (n : ℝ≥0) ≤ y := hy.1
    have hnN : n < N := by exact_mod_cast hny.trans_lt hyN
    exact hnN
