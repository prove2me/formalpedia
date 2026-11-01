-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exists_isCompact_eval_mem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:52:29.101994+00:00
-- url     : https://prove2.me/submissions/d772dbc7-cc3c-4a96-9e0d-245459640d65

import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Continuity_PathTightness_ad16da33
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Theorems.Thm_MarkovProcess_ContinuousPath_edist_le_of_modulus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact sets of paths, and tightness on continuous-path space

A family of laws on `C([0, ∞), alpha)` is tight as soon as two things hold uniformly over the
family: the time-zero position lies in a fixed compact set, and the oscillation over each bounded
time interval is controlled at a scale that does not depend on the law.  This file supplies the
compact sets that make that statement work and then assembles the tightness estimate.

The compact sets are `ContinuousPath.moduliSet K0 delta r`: the paths starting in `K0` whose
oscillation over `[0, n]` at scale `delta n` is at most `r n`, for every natural `n`.  When
`r n → 0` these conditions are exactly equicontinuity, so Arzelà--Ascoli applies as soon as the
values of the family at each fixed time stay in a compact set.  That last requirement --- the
compact containment condition of the weak-convergence literature --- is isolated as a hypothesis
in `isCompact_moduliSet_of_forall_isCompact`; over a *proper* metric state space (closed balls
compact) it is automatic, because the modulus already confines a path to a bounded neighbourhood
of its starting point, and `isCompact_moduliSet` discharges it.

Main results:

* `MarkovProcess.ContinuousPath.edist_le_of_modulus`, the chaining bound from the starting point;
* `MarkovProcess.ContinuousPath.moduliSet` and `moduliFunSet`, with closedness and
  equicontinuity;
* `MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact` and
  `isCompact_moduliSet`, the Arzelà--Ascoli compactness statements;
* `MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le`, tightness of a
  family of laws from a uniform modulus estimate and a compact time-zero law.

Nothing here constructs a law, and no compactness theorem for measures (Prokhorov's theorem) is
proved or used.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Metric Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha]

section Chaining



end Chaining

section Moduli















end Moduli

section Tight





end Tight

end ContinuousPath

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact sets of paths, and tightness on continuous-path space

A family of laws on `C([0, ∞), alpha)` is tight as soon as two things hold uniformly over the
family: the time-zero position lies in a fixed compact set, and the oscillation over each bounded
time interval is controlled at a scale that does not depend on the law.  This file supplies the
compact sets that make that statement work and then assembles the tightness estimate.

The compact sets are `ContinuousPath.moduliSet K0 delta r`: the paths starting in `K0` whose
oscillation over `[0, n]` at scale `delta n` is at most `r n`, for every natural `n`.  When
`r n → 0` these conditions are exactly equicontinuity, so Arzelà--Ascoli applies as soon as the
values of the family at each fixed time stay in a compact set.  That last requirement --- the
compact containment condition of the weak-convergence literature --- is isolated as a hypothesis
in `isCompact_moduliSet_of_forall_isCompact`; over a *proper* metric state space (closed balls
compact) it is automatic, because the modulus already confines a path to a bounded neighbourhood
of its starting point, and `isCompact_moduliSet` discharges it.

Main results:

* `MarkovProcess.ContinuousPath.edist_le_of_modulus`, the chaining bound from the starting point;
* `MarkovProcess.ContinuousPath.moduliSet` and `moduliFunSet`, with closedness and
  equicontinuity;
* `MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact` and
  `isCompact_moduliSet`, the Arzelà--Ascoli compactness statements;
* `MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le`, tightness of a
  family of laws from a uniform modulus estimate and a compact time-zero law.

Nothing here constructs a law, and no compactness theorem for measures (Prokhorov's theorem) is
proved or used.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha]











namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution [ProperSpace alpha] {K0 : Set alpha} (hK0 : IsCompact K0)
    {delta rho : ℕ → ℝ≥0∞} (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0))
    (t : ℝ≥0) :
    ∃ Q : Set alpha, IsCompact Q ∧ ∀ f ∈ moduliFunSet K0 delta rho, f t ∈ Q := by
  rcases K0.eq_empty_or_nonempty with hempty | ⟨c, hc⟩
  · refine ⟨∅, isCompact_empty, fun f hf ↦ ?_⟩
    rw [hempty] at hf
    exact absurd hf.1 (Set.notMem_empty _)
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall c).mp hK0.isBounded
  obtain ⟨n0, hn0⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨n, hnr, hnn⟩ :=
    ((hrho.eventually_lt_const (zero_lt_one (α := ℝ≥0∞))).and (eventually_ge_atTop n0)).exists
  set d : ℝ≥0 := (min (delta n) 1).toNNReal with hd
  have hdtop : min (delta n) 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hdcoe : (d : ℝ≥0∞) = min (delta n) 1 := by
    rw [hd, ENNReal.coe_toNNReal hdtop]
  have hdpos : 0 < d := by
    rw [← ENNReal.coe_pos, hdcoe]
    exact lt_min (hdelta n) one_pos
  have hdle : (d : ℝ≥0∞) ≤ delta n := by
    rw [hdcoe]
    exact min_le_left _ _
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hn0.trans (by exact_mod_cast hnn)
  set C : ℝ≥0∞ := ((⌈((n : ℝ≥0) : ℝ) / d⌉₊ + 1 : ℕ) : ℝ≥0∞) * rho n with hC
  have hCtop : C ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ne_top_of_lt (lt_of_lt_of_le hnr le_top))
  refine ⟨closedBall c (R + C.toReal), isCompact_closedBall _ _, fun f hf ↦ ?_⟩
  have hmod : ∀ s u : ℝ≥0, s ≤ (n : ℝ≥0) → u ≤ (n : ℝ≥0) → edist s u ≤ (d : ℝ≥0∞) →
      edist (f s) (f u) ≤ rho n := fun s u hs hu hsu ↦
    Set.mem_iInter.mp hf.2 n s u hs hu (hsu.trans hdle)
  have hchain := edist_le_of_modulus hdpos hmod htn
  have hdist : dist (f 0) (f t) ≤ C.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hCtop, ← edist_dist]
    exact hchain
  have h0 : dist (f 0) c ≤ R := mem_closedBall.mp (hR hf.1)
  rw [mem_closedBall]
  calc dist (f t) c ≤ dist (f t) (f 0) + dist (f 0) c := dist_triangle _ _ _
    _ ≤ C.toReal + R := add_le_add (by rw [dist_comm]; exact hdist) h0
    _ = R + C.toReal := add_comm _ _
