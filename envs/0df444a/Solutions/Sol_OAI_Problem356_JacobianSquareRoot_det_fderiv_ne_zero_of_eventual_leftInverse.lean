-- Prove2me | solution 1 for OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:14:30.609782+00:00
-- url     : https://prove2.me/submissions/dc1dd544-bbae-4237-9fdc-37a2464a8549

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
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport

open OAI OAI.Problem356
universe uIndex uE uD
open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise


theorem solution
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (F x))
    (hGF : ∀ᶠ y in nhds x, G (F y) = y) : (fderiv ℝ F x).det ≠ 0 := by
  have hcomp : fderiv ℝ G (F x) ∘L fderiv ℝ F x = ContinuousLinearMap.id ℝ E := by
    have h1 : HasFDerivAt (G ∘ F) (fderiv ℝ G (F x) ∘L fderiv ℝ F x) x :=
      hG.hasFDerivAt.comp x hF.hasFDerivAt
    have h2 : HasFDerivAt (G ∘ F) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).congr_of_eventuallyEq hGF
    exact h1.unique h2
  by_cases hfin : FiniteDimensional ℝ E
  · intro h0
    have := congrArg (fun L : E →L[ℝ] E => (L : E →ₗ[ℝ] E)) hcomp
    have h3 := congrArg LinearMap.det this
    simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at h3
    have hc : ((fderiv ℝ G (F x) ∘L fderiv ℝ F x : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        ((fderiv ℝ G (F x) : E →ₗ[ℝ] E) ∘ₗ (fderiv ℝ F x : E →ₗ[ℝ] E)) := rfl
    rw [hc, LinearMap.det_comp] at h3
    rw [ContinuousLinearMap.det] at h0
    rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  · rw [ContinuousLinearMap.det, LinearMap.det_eq_one_of_not_module_finite hfin]
    exact one_ne_zero

