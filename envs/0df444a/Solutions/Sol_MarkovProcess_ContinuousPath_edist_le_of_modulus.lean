-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.edist_le_of_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:27:16.594973+00:00
-- url     : https://prove2.me/submissions/5aa21cfd-740f-4b12-9a7a-ef67d78334bb

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
theorem solution {T d : ℝ≥0} (hd : 0 < d) {rho : ℝ≥0∞} {f : ℝ≥0 → alpha}
    (hf : ∀ s t : ℝ≥0, s ≤ T → t ≤ T → edist s t ≤ (d : ℝ≥0∞) → edist (f s) (f t) ≤ rho)
    {t : ℝ≥0} (ht : t ≤ T) :
    edist (f 0) (f t) ≤ ((⌈(T : ℝ) / d⌉₊ + 1 : ℕ) : ℝ≥0∞) * rho := by
  exact (by
    set K : ℕ := ⌈(T : ℝ) / d⌉₊ + 1 with hK
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      rw [hK]
      push_cast
      positivity
    have hKne : (K : ℝ≥0) ≠ 0 := by
      simpa only [ne_eq, Nat.cast_eq_zero] using Nat.succ_ne_zero _
    set u : ℕ → ℝ≥0 := fun k ↦ t * k / K with hu
    have hu0 : u 0 = 0 := by simp [hu]
    have huK : u K = t := by
      show t * (K : ℝ≥0) / (K : ℝ≥0) = t
      rw [mul_div_assoc, div_self hKne, mul_one]
    have hule : ∀ k, k ≤ K → u k ≤ T := by
      intro k hk
      refine le_trans ?_ ht
      rw [← NNReal.coe_le_coe]
      push_cast [hu]
      rw [div_le_iff₀ hKpos]
      have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk
      nlinarith [t.coe_nonneg, hkK]
    have hTK : (T : ℝ) / K < (d : ℝ) := by
      have hdpos : (0 : ℝ) < (d : ℝ) := hd
      have hceil : (T : ℝ) / d ≤ (⌈(T : ℝ) / d⌉₊ : ℝ) := Nat.le_ceil _
      have hlt : (T : ℝ) / d < (K : ℝ) := by
        rw [hK]
        push_cast
        linarith
      rw [div_lt_iff₀ hKpos]
      rw [div_lt_iff₀ hdpos] at hlt
      linarith
    have hstep : ∀ k : ℕ, edist (u k) (u (k + 1)) ≤ (d : ℝ≥0∞) := by
      intro k
      have hexp : ((u k : ℝ≥0) : ℝ) - ((u (k + 1) : ℝ≥0) : ℝ) = -((t : ℝ) / K) := by
        simp only [hu]
        push_cast
        rw [div_sub_div_same, ← mul_sub, show (k : ℝ) - ((k : ℝ) + 1) = -1 by ring]
        ring
      have hval : dist (u k) (u (k + 1)) = (t : ℝ) / K := by
        rw [NNReal.dist_eq, hexp, abs_neg, abs_of_nonneg (by positivity)]
      have htK : (t : ℝ) / K ≤ (d : ℝ) := by
        have hmono : (t : ℝ) / K ≤ (T : ℝ) / K := by gcongr
        linarith [hTK]
      rw [edist_dist, hval, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal htK
    have hchain : edist (f (u 0)) (f (u K)) ≤ ∑ _i ∈ Finset.Ico 0 K, rho :=
      edist_le_Ico_sum_of_edist_le (f := fun k ↦ f (u k)) (Nat.zero_le K)
        (d := fun _ ↦ rho) fun {k} _ hkK ↦
          hf (u k) (u (k + 1)) (hule k hkK.le) (hule (k + 1) hkK) (hstep k)
    rw [hu0, huK] at hchain
    simpa only [Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul] using hchain
  )
