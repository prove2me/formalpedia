-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:55.742165+00:00
-- url     : https://prove2.me/submissions/aa0c95e6-2aaf-4fb5-8ac7-3eb19d72e341

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
import Theorems.Thm_MarkovProcess_ContinuousPath_equicontinuous_moduliFunSet

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





theorem isClosed_moduliFunSet {K0 : Set alpha} (hK0 : IsClosed K0) (delta rho : ℕ → ℝ≥0∞) :
    IsClosed (moduliFunSet K0 delta rho) := by
  refine IsClosed.inter (hK0.preimage (continuous_apply (0 : ℝ≥0))) (isClosed_iInter fun n ↦ ?_)
  have hrewrite : {f : ℝ≥0 → alpha | ∀ s t : ℝ≥0, s ≤ (n : ℝ≥0) → t ≤ (n : ℝ≥0) →
        edist s t ≤ delta n → edist (f s) (f t) ≤ rho n} =
      ⋂ s : ℝ≥0, ⋂ t : ℝ≥0, ⋂ _ : s ≤ (n : ℝ≥0), ⋂ _ : t ≤ (n : ℝ≥0),
        ⋂ _ : edist s t ≤ delta n, {f : ℝ≥0 → alpha | edist (f s) (f t) ≤ rho n} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrewrite]
  refine isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_
  exact isClosed_le ((continuous_apply s).edist (continuous_apply t)) continuous_const









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
theorem solution {K0 : Set alpha} (hK0 : IsClosed K0)
    {delta rho : ℕ → ℝ≥0∞} (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0))
    (hpoint : ∀ t : ℝ≥0, ∃ Q : Set alpha, IsCompact Q ∧
      ∀ f ∈ moduliFunSet K0 delta rho, f t ∈ Q) :
    IsCompact (moduliSet K0 delta rho) := by
  have hequi := equicontinuous_moduliFunSet (K0 := K0) hdelta hrho
  choose Q hQcompact hQmem using hpoint
  have hfun : IsCompact (moduliFunSet K0 delta rho) :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi hQcompact)
      (isClosed_moduliFunSet hK0 delta rho)
      fun f hf ↦ Set.mem_univ_pi.mpr fun t ↦ hQmem t f hf
  have himage : ContinuousMap.toFun '' moduliSet K0 delta rho = moduliFunSet K0 delta rho := by
    ext f
    constructor
    · rintro ⟨omega, homega, rfl⟩
      exact ⟨homega.1, Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp homega.2 n⟩
    · intro hf
      exact ⟨⟨f, hequi.continuous ⟨f, hf⟩⟩,
        ⟨hf.1, Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp hf.2 n⟩, rfl⟩
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ ?_
  · rw [himage]
    exact hfun
  · exact hequi.comp fun w : moduliSet K0 delta rho ↦
      (⟨((w : ContinuousPath alpha) : ℝ≥0 → alpha),
        ⟨w.2.1, Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp w.2.2 n⟩⟩ :
          moduliFunSet K0 delta rho)
