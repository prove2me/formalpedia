-- Prove2me | solution 1 for OAI.Problem356.finite_eventual_neighborhoods
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:54:58.92766+00:00
-- url     : https://prove2.me/submissions/6bd9f199-4102-4860-b539-0bfde6740835

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate

open OAI OAI.Problem356
universe uIndex uX uY
open Set Filter Metric
open scoped ENNReal


theorem solution {ι : Type uIndex} {X : Type uX} [PseudoMetricSpace X]
    (s : Finset ι) (p : ι → X) (P : ι → X → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x in nhds (p i), P i x) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → P i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨r, hr, hrs⟩ := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    obtain ⟨ra, hra, hras⟩ := Metric.eventually_nhds_iff.mp (hP a (Finset.mem_insert_self a s))
    refine ⟨min r ra, lt_min hr hra, fun i hi x hx => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hras (lt_of_lt_of_le hx (min_le_right _ _))
    · exact hrs i hi' x (lt_of_lt_of_le hx (min_le_left _ _))

