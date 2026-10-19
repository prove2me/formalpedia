-- Prove2me | solution 2 for OAI.Problem356.strictConvex_eq_iff_of_hasFDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:12:06.842501+00:00
-- url     : https://prove2.me/submissions/d0ee49ab-e417-4173-b762-88ac0f7aa5c3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean:L33-L48
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.strictConvex_eq_iff_of_hasFDerivAt_zero. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_convex_isMinOn_of_hasFDerivAt_zero

-- ---- from OAI.Analysis.CoulombTransport.StrictMinimum ----
namespace OAI

universe uE uP

noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict convexity upgrades a stationary point to the unique minimum. -/
theorem strictConvex_eq_iff_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : StrictConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) {y : E} (hy : y ∈ s) :
    f y = f x ↔ y = x := by
  have hmin := convex_isMinOn_of_hasFDerivAt_zero hf.convexOn hx hd
  constructor
  · intro heq
    have hymin : IsMinOn f s y := by
      intro z hz
      change f y ≤ f z
      rw [heq]
      exact hmin hz
    exact hf.eq_of_isMinOn hymin hmin hy hx
  · rintro rfl
    rfl

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.strictConvex_eq_iff_of_hasFDerivAt_zero.{uE} := @_root_.OAI.Problem356.strictConvex_eq_iff_of_hasFDerivAt_zero.{uE}
