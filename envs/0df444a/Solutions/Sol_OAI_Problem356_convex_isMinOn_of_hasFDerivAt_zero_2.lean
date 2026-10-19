-- Prove2me | solution 2 for OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:10:31.34245+00:00
-- url     : https://prove2.me/submissions/a3c7fa4e-c1af-43b4-8048-66c0f6953be0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean:L16-L31
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.StrictMinimum ----
namespace OAI

universe uE uP

noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A stationary point of a convex differentiable function is a global minimizer
on its convexity domain. -/
theorem convex_isMinOn_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := by
  intro y hy
  have hline := hf.comp_affineMap (AffineMap.lineMap x y)
  have hderiv : HasDerivAt (f ∘ AffineMap.lineMap x y) 0 (0 : ℝ) := by
    have hd' : HasFDerivAt f (0 : E →L[ℝ] ℝ) ((AffineMap.lineMap x y) (0 : ℝ)) := by
      simpa using hd
    have h := hd'.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap : HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ))
    simpa using h
  have hle := hline.le_slope_of_hasDerivAt
    (by simpa using hx) (by simpa using hy) (by norm_num : (0 : ℝ) < 1) hderiv
  simpa [slope_def_field] using hle

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero.{uE} := @_root_.OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero.{uE}
