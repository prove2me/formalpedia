-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.equicontinuous_moduliFunSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:27:28.298528+00:00
-- url     : https://prove2.me/submissions/2d29048c-74fd-4326-91d1-bdc902315047

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
theorem solution {K0 : Set alpha} {delta rho : ℕ → ℝ≥0∞}
    (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0)) :
    Equicontinuous fun f : moduliFunSet K0 delta rho ↦ (f : ℝ≥0 → alpha) := by
  intro t0
  rw [equicontinuousAt_iff]
  intro eps heps
  obtain ⟨n0, hn0⟩ := exists_nat_ge ((t0 : ℝ) + 1)
  obtain ⟨n, hnr, hnn⟩ :=
    ((hrho.eventually_lt_const (ENNReal.ofReal_pos.mpr heps)).and
      (eventually_ge_atTop n0)).exists
  set d : ℝ≥0∞ := min (delta n) 1 with hd
  have hdpos : 0 < d := lt_min (hdelta n) one_pos
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hdreal : 0 < d.toReal := ENNReal.toReal_pos hdpos.ne' hdtop
  have hdle1 : d.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (min_le_right (delta n) 1)
  have hnreal : (t0 : ℝ) + 1 ≤ (n : ℝ) := by
    refine hn0.trans ?_
    exact_mod_cast hnn
  have ht0n : t0 ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  refine ⟨d.toReal, hdreal, fun s hs f ↦ ?_⟩
  have hsdist : |(s : ℝ) - (t0 : ℝ)| < d.toReal := by
    rw [← NNReal.dist_eq]
    exact hs
  have hsn : s ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have := (abs_lt.mp hsdist).2
    linarith
  have hedist : edist t0 s ≤ delta n := by
    have hlt : edist t0 s < d := by
      rw [edist_comm, edist_dist, ← ENNReal.ofReal_toReal hdtop]
      exact (ENNReal.ofReal_lt_ofReal_iff hdreal).mpr hs
    exact hlt.le.trans (min_le_left _ _)
  have hmod := Set.mem_iInter.mp f.2.2 n (t0 : ℝ≥0) s ht0n hsn hedist
  have hkey : ENNReal.ofReal (dist ((f : ℝ≥0 → alpha) t0) ((f : ℝ≥0 → alpha) s)) <
      ENNReal.ofReal eps := by
    rw [← edist_dist]
    exact lt_of_le_of_lt hmod hnr
  exact (ENNReal.ofReal_lt_ofReal_iff heps).mp hkey
