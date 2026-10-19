-- Prove2me | solution 2 for OAI.Problem356.bilinear_coercive_of_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:18:10.54391+00:00
-- url     : https://prove2.me/submissions/ae464327-28d3-4b66-bc8b-b11c8aa8980c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/HessianCoercivity.lean:L12-L29
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.bilinear_coercive_of_norm_sub_le. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.HessianCoercivity ----
namespace OAI

universe uE uX

open Filter
open scoped Topology

namespace Problem356

/-- A quantitative lower bound on a bilinear form survives a small operator-norm
perturbation. No finite-dimensional hypothesis is needed. -/
theorem bilinear_coercive_of_norm_sub_le
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (a δ : ℝ)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (hclose : ‖C - B‖ ≤ δ) :
    ∀ v, (a - δ) * ‖v‖ ^ 2 ≤ C v v := by
  intro v
  have hv := (C - B).le_opNorm₂ v v
  have hmul : ‖C - B‖ * ‖v‖ * ‖v‖ ≤ δ * ‖v‖ ^ 2 := by
    calc
      ‖C - B‖ * ‖v‖ * ‖v‖ = ‖C - B‖ * ‖v‖ ^ 2 := by ring
      _ ≤ δ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hclose (sq_nonneg _)
  have hdiff : |C v v - B v v| ≤ δ * ‖v‖ ^ 2 := by
    simpa only [sub_apply, Real.norm_eq_abs] using hv.trans hmul
  have hlo := (abs_le.mp hdiff).1
  have hb := hB v
  nlinarith

end Problem356

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.bilinear_coercive_of_norm_sub_le.{uE} := @_root_.OAI.Problem356.bilinear_coercive_of_norm_sub_le.{uE}
