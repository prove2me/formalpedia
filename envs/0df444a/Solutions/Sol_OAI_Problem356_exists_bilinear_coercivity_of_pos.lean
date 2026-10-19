-- Prove2me | solution 1 for OAI.Problem356.exists_bilinear_coercivity_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:58:09.731878+00:00
-- url     : https://prove2.me/submissions/9af9c234-8b0a-4f43-ab3f-036eb2dcce21

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
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity

open OAI OAI.Problem356
universe uE uX
open Filter
open scoped Topology


theorem solution
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ a : ℝ, 0 < a ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim v 0
    subst this; simp
  have hc : Continuous fun v : E => B v v := by fun_prop
  obtain ⟨v0, hv0, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
  have hv0ne : v0 ≠ 0 := by
    intro h; rw [h] at hv0; simp at hv0
  refine ⟨B v0 v0, hpos v0 hv0ne, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set w := ‖v‖⁻¹ • v with hw
  have hws : w ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h1 := hmin hws
  simp only [Set.mem_setOf_eq] at h1
  have hvw : v = ‖v‖ • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have h2 : B v v = ‖v‖ ^ 2 * B w w := by
    conv_lhs => rw [hvw]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h2]
  have := sq_nonneg ‖v‖
  nlinarith

