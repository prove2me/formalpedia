-- Prove2me | solution 2 for OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:45:23.177689+00:00
-- url     : https://prove2.me/submissions/32abda69-8bee-4011-92f8-31275f6f1fde

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/JacobianSquareRoot.lean:L82-L98
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.CoulombTransport.JacobianSquareRoot ----
namespace OAI

universe uIndex uE uD

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace Problem356.JacobianSquareRoot

/-- An eventually defined differentiable left inverse forces a nonzero derivative determinant. -/
theorem det_fderiv_ne_zero_of_eventual_leftInverse
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (F x))
    (hGF : ∀ᶠ y in nhds x, G (F y) = y) : (fderiv ℝ F x).det ≠ 0 := by
  have hc : (fderiv ℝ G (F x)).comp (fderiv ℝ F x) =
      ContinuousLinearMap.id ℝ E :=
    (hG.hasFDerivAt.comp x hF.hasFDerivAt).unique
      ((hasFDerivAt_id x).congr_of_eventuallyEq hGF)
  have hprod := congrArg (fun A : E →L[ℝ] E => A.det) hc
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hprod
  change (fderiv ℝ G (F x)).det * (fderiv ℝ F x).det = 1 at hprod
  intro hz
  rw [hz, mul_zero] at hprod
  exact zero_ne_one hprod

end Problem356.JacobianSquareRoot

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.JacobianSquareRoot
open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse.{uE} := @_root_.OAI.Problem356.JacobianSquareRoot.det_fderiv_ne_zero_of_eventual_leftInverse.{uE}
