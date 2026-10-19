-- Prove2me | solution 1 for OAI.Problem356.bilinear_coercive_of_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:55:29.609759+00:00
-- url     : https://prove2.me/submissions/11d50517-74c8-41fd-9ab2-f8b10de2534d

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
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (a δ : ℝ)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (hclose : ‖C - B‖ ≤ δ) :
    ∀ v, (a - δ) * ‖v‖ ^ 2 ≤ C v v := by
  intro v
  have h1 := hB v
  have h2 : |(C - B) v v| ≤ δ * ‖v‖ ^ 2 := by
    calc |(C - B) v v| = ‖(C - B) v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖C - B‖ * ‖v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ δ * ‖v‖ * ‖v‖ := by gcongr
      _ = δ * ‖v‖ ^ 2 := by ring
  have h3 : C v v = B v v + (C - B) v v := by simp
  have h4 := (abs_le.mp h2).1
  rw [h3]
  nlinarith

