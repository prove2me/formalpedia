-- Prove2me | solution 1 for OAI.Problem356.ae_branchMarginal_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:15:02.134996+00:00
-- url     : https://prove2.me/submissions/3abc98b9-bafb-4f1a-8980-a0695a611a41

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution (nu : Measure E3) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) {B U : Set E3}
    (hU : MeasurableSet U) (hfull : ∀ᵐ x ∂nu, x ∈ B)
    (hBU : B ⊆ U) (hHU : ∀ i, H i '' B ⊆ U) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U := by
  rw [ae_iff]
  have hc : MeasurableSet {x : E3 | ¬ x ∈ U} := hU.compl
  have key : ∀ i, Measure.map (H i) nu {x : E3 | ¬ x ∈ U} = 0 := by
    intro i
    rw [Measure.map_apply (hH i) hc]
    apply ae_iff.mp
    filter_upwards [hfull] with x hx
    exact hHU i ⟨x, hx, rfl⟩
  have h0 : nu {x : E3 | ¬ x ∈ U} = 0 := by
    apply ae_iff.mp
    filter_upwards [hfull] with x hx
    exact hBU hx
  simp only [branchMarginal, Measure.smul_apply, Measure.add_apply, smul_eq_mul, key, h0]
  simp

