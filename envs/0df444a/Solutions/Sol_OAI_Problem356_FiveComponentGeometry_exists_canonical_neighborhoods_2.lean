-- Prove2me | solution 2 for OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:03:48.576992+00:00
-- url     : https://prove2.me/submissions/b8a0bfd8-fc15-41fe-a32d-e8ceb7bdb31a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/FiveComponentCanonical.lean:L14-L91
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Theorems.Thm_OAI_Problem356_FiveComponentGeometry_ennreal_local_certificate
import Theorems.Thm_OAI_Problem356_Geometry_finite_disjoint_closedBalls_subset

-- ---- from OAI.Analysis.CoulombTransport.CenterCertificate ----
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.CenterCertificate

theorem point_injective : Function.Injective point := by
  intro i j h
  have h0 := congrArg (fun x : E3 => x 0) h
  have h1 := congrArg (fun x : E3 => x 1) h
  clear h
  fin_cases i <;> fin_cases j
  all_goals norm_num [point] at h0
  all_goals norm_num [point] at h1
  all_goals rfl

end Problem356.CenterCertificate

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

lemma point_two_eq_neg : point 2 = -point 1 := by
  change (!₂[-1, 0, 0] : E3) = -(!₂[1, 0, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma point_four_eq_neg : point 4 = -point 3 := by
  change (!₂[0, -1, 0] : E3) = -(!₂[0, 1, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentCanonical ----
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal

namespace Problem356.FiveComponentGeometry

open CenterCertificate GoodTypePermutation

/-- Common component neighborhoods on which both canonical Coulomb
certificates hold, including their one-way symmetric contact localization. -/
theorem exists_canonical_neighborhoods
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ W : Fin 5 → Set E3,
      (∀ i, W i ∈ nhds (point i)) ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2 ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4 := by
  let R : Fin 5 → ℝ :=
    ![min C₁.stateRadius C₂.stateRadius, C₁.parameterRadius, C₁.stateRadius,
      C₂.parameterRadius, C₂.stateRadius]
  have hR : ∀ i, 0 < R i := by
    intro i
    fin_cases i
    · exact lt_min C₁.stateRadius_pos C₂.stateRadius_pos
    · exact C₁.parameterRadius_pos
    · exact C₁.stateRadius_pos
    · exact C₂.parameterRadius_pos
    · exact C₂.stateRadius_pos
  obtain ⟨r, hr, hsub, hdisj⟩ := Geometry.finite_disjoint_closedBalls_subset
    point point_injective (fun i => ball (point i) (R i))
    (fun _ => isOpen_ball) (fun i => mem_ball_self (hR i))
  let W : Fin 5 → Set E3 := fun i => ball (point i) r
  have hWsub (i : Fin 5) : W i ⊆ ball (point i) (R i) :=
    ball_subset_closedBall.trans (hsub i)
  have hdist {i j : Fin 5} (hij : i ≠ j) {x y : E3}
      (hx : x ∈ W i) (hy : y ∈ W j) : 0 < dist x y := by
    apply dist_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdisj hij)
      (heq ▸ ball_subset_closedBall hx) (ball_subset_closedBall hy)
  refine ⟨W, (fun i => ball_mem_nhds (point i) hr), ?_, ?_⟩
  · intro x hx y hy z hz
    have hx' := hWsub 0 hx
    change x ∈ ball (0 : E3) (min C₁.stateRadius C₂.stateRadius) at hx'
    have hx₁ : x ∈ ball (0 : E3) C₁.stateRadius :=
      ball_subset_ball (min_le_left _ _) hx'
    have hy₁ : y ∈ ball (point 1) C₁.parameterRadius := hWsub 1 hy
    have hz₁ : z ∈ ball (-point 1) C₁.stateRadius := by
      have hz' := hWsub 2 hz
      change z ∈ ball (point 2) C₁.stateRadius at hz'
      simpa only [point_two_eq_neg] using hz'
    have hc := ennreal_local_certificate C₁ hy₁ hx₁ hz₁
      (hdist (by decide : (0 : Fin 5) ≠ 1) hx hy)
      (hdist (by decide : (0 : Fin 5) ≠ 2) hx hz)
      (hdist (by decide : (1 : Fin 5) ≠ 2) hy hz)
    refine ⟨hc.1, ?_⟩
    intro heq
    obtain ⟨hxc, hzc⟩ := hc.2.mp heq
    apply Or.inl
    refine ⟨y, ?_, ?_⟩
    · rw [C₁.source_ball]
      exact hy₁
    · simpa only [hxc, hzc] using
        (List.Perm.refl [C₁.charts.central y, y, C₁.charts.opposite y])
  · intro x hx y hy z hz
    have hx' := hWsub 0 hx
    change x ∈ ball (0 : E3) (min C₁.stateRadius C₂.stateRadius) at hx'
    have hx₂ : x ∈ ball (0 : E3) C₂.stateRadius :=
      ball_subset_ball (min_le_right _ _) hx'
    have hy₂ : y ∈ ball (point 3) C₂.parameterRadius := hWsub 3 hy
    have hz₂ : z ∈ ball (-point 3) C₂.stateRadius := by
      have hz' := hWsub 4 hz
      change z ∈ ball (point 4) C₂.stateRadius at hz'
      simpa only [point_four_eq_neg] using hz'
    have hc := ennreal_local_certificate C₂ hy₂ hx₂ hz₂
      (hdist (by decide : (0 : Fin 5) ≠ 3) hx hy)
      (hdist (by decide : (0 : Fin 5) ≠ 4) hx hz)
      (hdist (by decide : (3 : Fin 5) ≠ 4) hy hz)
    refine ⟨hc.1, ?_⟩
    intro heq
    obtain ⟨hxc, hzc⟩ := hc.2.mp heq
    apply Or.inr
    refine ⟨y, ?_, ?_⟩
    · rw [C₂.source_ball]
      exact hy₂
    · simpa only [hxc, hzc] using
        (List.Perm.refl [C₂.charts.central y, y, C₂.charts.opposite y])

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal
open CenterCertificate GoodTypePermutation


theorem solution : type_of% @_root_.OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods := @_root_.OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods
