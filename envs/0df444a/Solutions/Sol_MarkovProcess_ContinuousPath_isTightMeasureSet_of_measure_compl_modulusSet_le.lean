-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:58:38.326273+00:00
-- url     : https://prove2.me/submissions/dcf739d9-f84d-4f36-a81a-96d2fffbccd5

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
import Theorems.Thm_MarkovProcess_ContinuousPath_exists_isCompact_eval_mem
import Theorems.Thm_MarkovProcess_ContinuousPath_isCompact_moduliSet_of_forall_isCompact

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













/-- **Compactness of a modulus class over a proper state space.**  Over a metric state space whose
closed balls are compact, the continuous paths starting in a compact set and obeying a vanishing
sequence of moduli form a compact subset of path space. -/
theorem isCompact_moduliSet [ProperSpace alpha] {K0 : Set alpha} (hK0 : IsCompact K0)
    {delta rho : ℕ → ℝ≥0∞} (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0)) :
    IsCompact (moduliSet K0 delta rho) :=
  isCompact_moduliSet_of_forall_isCompact hK0.isClosed hdelta hrho
    (exists_isCompact_eval_mem hK0 hdelta hrho)

end Moduli

section Tight

private theorem tsum_geometric_half (eps : ℝ≥0∞) :
    (∑' n : ℕ, eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) = eps := by
  have hsplit : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ = 2⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), ← ENNReal.inv_pow]
    ring
  have hone : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [← ENNReal.inv_two_add_inv_two, ENNReal.add_sub_cancel_left (by simp)]
  rw [ENNReal.tsum_mul_left]
  simp_rw [hsplit]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hone, inv_inv,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]



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
theorem solution [ProperSpace alpha]
    {S : Set (Measure (ContinuousPath alpha))} {K0 : Set alpha} (hK0 : IsCompact K0)
    (hstart : ∀ mu ∈ S, mu {omega : ContinuousPath alpha | omega 0 ∉ K0} = 0)
    (hmod : ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ mu ∈ S, mu (modulusSet T delta r)ᶜ ≤ eps) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro eps heps
  set rho : ℕ → ℝ≥0∞ := fun n ↦ ((n : ℝ≥0∞))⁻¹ with hrho
  have hrhopos : ∀ n : ℕ, 0 < rho n := fun n ↦ ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
  have hrhotendsto : Tendsto rho atTop (nhds 0) := ENNReal.tendsto_inv_nat_nhds_zero
  have hepsn : ∀ n : ℕ, 0 < eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ :=
    fun n ↦ ENNReal.mul_pos heps.ne' (by simp)
  choose delta hdelta hdeltaS using fun n : ℕ ↦
    hmod (n : ℝ≥0) (rho n) (hrhopos n) _ (hepsn n)
  refine ⟨moduliSet K0 delta rho, isCompact_moduliSet hK0 hdelta hrhotendsto, fun mu hmu ↦ ?_⟩
  have hcompl : (moduliSet K0 delta rho)ᶜ =
      {omega : ContinuousPath alpha | omega 0 ∉ K0} ∪
        ⋃ n : ℕ, (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ := by
    ext omega
    simp only [moduliSet, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Set.mem_union, Set.mem_iUnion, not_and_or, not_forall]
  rw [hcompl]
  calc mu ({omega : ContinuousPath alpha | omega 0 ∉ K0} ∪
          ⋃ n : ℕ, (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ)
      ≤ mu {omega : ContinuousPath alpha | omega 0 ∉ K0} +
        mu (⋃ n : ℕ, (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ) := measure_union_le _ _
    _ ≤ 0 + ∑' n : ℕ, mu (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ :=
        add_le_add (hstart mu hmu).le (measure_iUnion_le _)
    _ ≤ ∑' n : ℕ, eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
        rw [zero_add]
        exact ENNReal.tsum_le_tsum fun n ↦ hdeltaS n mu hmu
    _ = eps := tsum_geometric_half eps
