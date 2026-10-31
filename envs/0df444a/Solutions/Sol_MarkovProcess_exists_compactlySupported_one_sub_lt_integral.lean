-- Prove2me | solution 1 for MarkovProcess.exists_compactlySupported_one_sub_lt_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:08.039466+00:00
-- url     : https://prove2.me/submissions/73439c50-77b5-4faa-a33f-46985bd76c84

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported

namespace MarkovProcess

variable {X : Type*} [MeasurableSpace X]







end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported


variable {X : Type*} [MeasurableSpace X]

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution [PseudoEMetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X] [LocallyCompactSpace X]
    [T2Space X] (mu : Measure X) [IsProbabilityMeasure mu] {eps : ℝ} (heps : 0 < eps) :
    ∃ g : C_c(X, ℝ), (∀ y, g y ∈ Set.Icc (0 : ℝ) 1) ∧ 1 - eps < ∫ y, g y ∂mu := by
  have htight : IsTightMeasureSet ({mu} : Set (Measure X)) := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨K, hK, hKmu⟩ := htight (ENNReal.ofReal (eps / 2)) (by positivity)
  simp only [Set.mem_singleton_iff, forall_eq] at hKmu
  obtain ⟨g, hgK, -, hgsupp, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  refine ⟨⟨g, hgsupp⟩, hg01, ?_⟩
  show (1 : ℝ) - eps < ∫ y, g y ∂mu
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKcompl : mu.real Kᶜ ≤ eps / 2 := by
    have h := ENNReal.toReal_mono (by simp) hKmu
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hint : Integrable (fun y ↦ g y) mu :=
    g.continuous.integrable_of_hasCompactSupport hgsupp
  have hlow : mu.real K ≤ ∫ y, g y ∂mu := by
    rw [← integral_indicator_one hKmeas]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hKmeas) hint fun y ↦ ?_
    by_cases hy : y ∈ K
    · simp only [Set.indicator_of_mem hy, Pi.one_apply]
      exact le_of_eq (hgK hy).symm
    · simp only [Set.indicator_of_notMem hy]
      exact (hg01 y).1
  have huniv : mu.real K + mu.real Kᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hKmeas, probReal_univ]
  linarith
