-- Prove2me | solution 2 for OAI.Problem356.Geometry.finite_disjoint_closedBalls
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:36:12.277207+00:00
-- url     : https://prove2.me/submissions/82fd30c3-9037-4f5d-a146-b834727a6d44

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/NeighborhoodCertificate.lean:L44-L61
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Geometry.finite_disjoint_closedBalls. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_Geometry_exists_uniform_positive_radius

-- ---- from OAI.Analysis.CoulombTransport.NeighborhoodCertificate ----
namespace OAI

universe uIndex uX

noncomputable section

open Filter Metric Set

namespace Problem356.Geometry

/-- Distinct finitely many centers admit a common positive radius with
pairwise disjoint closed balls. -/
theorem finite_disjoint_closedBalls {ι : Type uIndex} {X : Type uX} [Finite ι] [MetricSpace X]
    (a : ι → X) (ha : Function.Injective a) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (fun i j =>
      Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  let J := {q : ι × ι // q.1 ≠ q.2}
  let r : J → ℝ := fun q => dist (a q.val.1) (a q.val.2) / 3
  have hr : ∀ q, 0 < r q := by
    intro q
    exact div_pos (dist_pos.mpr (ha.ne q.property)) (by norm_num)
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_positive_radius r hr
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  apply Metric.closedBall_disjoint_closedBall
  have h := hbound ⟨(i, j), hij⟩
  change δ ≤ dist (a i) (a j) / 3 at h
  linarith

end Problem356.Geometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Geometry
open Filter Metric Set


theorem solution.{uIndex,uX} : type_of% @_root_.OAI.Problem356.Geometry.finite_disjoint_closedBalls.{uIndex,uX} := @_root_.OAI.Problem356.Geometry.finite_disjoint_closedBalls.{uIndex,uX}
