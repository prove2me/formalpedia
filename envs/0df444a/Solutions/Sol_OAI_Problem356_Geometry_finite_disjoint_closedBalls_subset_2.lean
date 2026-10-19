-- Prove2me | solution 2 for OAI.Problem356.Geometry.finite_disjoint_closedBalls_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:38:37.288297+00:00
-- url     : https://prove2.me/submissions/f2d35f93-724e-48c2-ac11-8990714e486b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/NeighborhoodCertificate.lean:L63-L89
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Geometry.finite_disjoint_closedBalls_subset. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_Geometry_finite_disjoint_closedBalls

-- ---- from OAI.Analysis.CoulombTransport.NeighborhoodCertificate ----
namespace OAI

universe uIndex uX

noncomputable section

open Filter Metric Set

namespace Problem356.Geometry

/-- One radius may simultaneously separate all components and keep each
closed component ball inside a prescribed open neighborhood. -/
theorem finite_disjoint_closedBalls_subset {ι : Type uIndex} {X : Type uX} [Finite ι]
    [MetricSpace X] (a : ι → X) (ha : Function.Injective a)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (haU : ∀ i, a i ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, closedBall (a i) δ ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  have hlocal : ∀ i, ∃ r : ℝ, 0 < r ∧ ball (a i) r ⊆ U i := by
    intro i
    exact Metric.isOpen_iff.mp (hU i) (a i) (haU i)
  choose r hr hsub using hlocal
  obtain ⟨ε, hε, hεr⟩ := exists_uniform_positive_radius r hr
  obtain ⟨η, hη, hdisj⟩ := finite_disjoint_closedBalls a ha
  refine ⟨min (ε / 2) η, lt_min (half_pos hε) hη, ?_, ?_⟩
  · intro i x hx
    apply hsub i
    rw [mem_ball]
    have hx' : dist x (a i) ≤ min (ε / 2) η := hx
    have hsmall : min (ε / 2) η ≤ ε / 2 := min_le_left _ _
    have hri := hεr i
    linarith
  · intro i j hij
    exact (hdisj hij).mono
      (closedBall_subset_closedBall (min_le_right _ _))
      (closedBall_subset_closedBall (min_le_right _ _))

end Problem356.Geometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Geometry
open Filter Metric Set


theorem solution.{uIndex,uX} : type_of% @_root_.OAI.Problem356.Geometry.finite_disjoint_closedBalls_subset.{uIndex,uX} := @_root_.OAI.Problem356.Geometry.finite_disjoint_closedBalls_subset.{uIndex,uX}
