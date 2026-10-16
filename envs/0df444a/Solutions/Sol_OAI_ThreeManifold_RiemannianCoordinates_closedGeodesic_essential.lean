-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.closedGeodesic_essential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:24:17.16784+00:00
-- url     : https://prove2.me/submissions/3abeb6cb-6cad-44f9-bcf9-974e5429d95a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Continuation.lean:L871-L898
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.closedGeodesic_essential. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Theorems.Thm_OAI_ThreeManifold_PathContinuation_ncp_exponential_lift_compact_bounds

-- ---- from OAI.Geometry.ConjugatePoints.Continuation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Geodesic continuation and the covering exponential map.
-/

section
open Set Filter Topology
namespace ThreeManifold.FlowContinuation.Equation
variable {X : Type*} (P : Equation X)

end ThreeManifold.FlowContinuation.Equation

namespace ThreeManifold.PathContinuation
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Y]
variable (f : E → Y) (γ : ℝ → Y)
end ThreeManifold.PathContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}
open RiemannianCoordinates

end ThreeManifold.PathContinuation
end

section
open Set Filter Topology
namespace ThreeManifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}

variable [CompactSpace M] [T2Space M]

end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M] {γ : ℝ → M}

end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology unitInterval
namespace ThreeManifold
variable {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
variable {p : E → X}

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
local notation "𝕀" => unitInterval
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

theorem ncp_exponential_path_lift (g : SmoothMetric M)
    (hn : NoConjugatePoints g) (p : M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ)
    (v0 : E3) (hv0 : exponential g p v0 = γ 0) :
    ∃ v : ℝ → E3, ContDiff ℝ 1 v ∧ v 0 = v0 ∧ ∀ t, exponential g p (v t) = γ t := by
  let f := exponential g p
  have hf := exponential_contMDiff g p
  have hi := exponential_mfderiv_injective g hn p
  let hl := exponential_isLocalHomeomorph g hn p
  let x : State f γ := ⟨(0,v0),hv0⟩
  obtain ⟨z,hz0,hz⟩ := (equation f γ hl).exists_global_of_compact_bounds
    (fun y => local_lift_exists hf hi hl hγ y)
    (fun A hA => ncp_exponential_lift_compact_bounds g hn p hγ x A hA)
  have htime : ∀ t, (z t).val.1 = t := by
    have h := isOpen_univ.eqOn_of_deriv_eq (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      (fun t _ => (holds_time_derivative f γ (hz t)).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
      (fun t _ => by rw [(holds_time_derivative f γ (hz t)).deriv]; simp)
      (mem_univ 0) (show (z 0).val.1 = (id 0 : ℝ) by rw [hz0]; rfl)
    exact fun t => h (mem_univ t)
  let v : ℝ → E3 := fun t => (z t).val.2
  have hvc : Continuous v := continuous_iff_continuousAt.mpr
    (fun t => (holds_space_derivative f γ (hz t)).continuousAt)
  have he : ∀ t, f (v t) = γ t := fun t => (z t).property.trans (congrArg γ (htime t))
  exact ⟨v,contDiff_lift_of_localHomeomorph hf hi hl hγ hvc he,
    show v 0 = v0 by change (z 0).val.2 = v0; rw [hz0],he⟩

theorem ncp_exponential_isCoveringMap (g : SmoothMetric M)
    (hn : NoConjugatePoints g) (p : M) : IsCoveringMap (exponential g p) :=
  covering_of_global_smooth_lifts (exponential_isLocalHomeomorph g hn p)
    (fun hγ v0 hv0 => ncp_exponential_path_lift g hn p hγ v0 hv0)
end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

theorem closedGeodesic_essential (g : SmoothMetric M) (hn : NoConjugatePoints g)
    {γ : ℝ → M} (hγ : IsGeodesicOn g γ univ) (he : γ 1 = γ 0)
    (hv : (velocity γ 0 : E3) ≠ 0) :
    (Path.Homotopic.Quotient.mk (closedCurvePath (contMDiffOn_univ.mp hγ.1).continuous he) :
      FundamentalGroup M (γ 0)) ≠ (1 : FundamentalGroup M (γ 0)) := by
  let p := γ 0
  let v : E3 := velocity γ 0
  let f := exponential g p
  let hp := ncp_exponential_isCoveringMap g hn p
  have hpath (t : ℝ) : f (t • v) = γ t := by
    change exponential g p (t • v) = γ t
    rw [exponential_scale]
    exact geodesic_unique g isOpen_univ ordConnected_univ
      (globalGeodesic_isGeodesic g (fiberPhase p v)) hγ (mem_univ 0)
      (globalGeodesic_initial g (fiberPhase p v)) (mem_univ t)
  let P := closedCurvePath (contMDiffOn_univ.mp hγ.1).continuous he
  have hP0 : P 0 = f 0 := (exponential_zero g p).symm
  have hl : (fun t : unitInterval => (t : ℝ) • v) = hp.liftPath P 0 hP0 := by
    apply (hp.eq_liftPath_iff hP0).2
    exact ⟨continuous_subtype_val.smul continuous_const,funext (fun t => hpath t),by simp⟩
  intro hnull
  have hmono := congrArg (fun k : FundamentalGroup M p =>
    (hp.monodromy k ⟨0,exponential_zero g p⟩).val) hnull
  change hp.liftPath P 0 hP0 1 = (hp.monodromy (.refl p) ⟨0,exponential_zero g p⟩).val at hmono
  rw [hp.monodromy_refl] at hmono
  rw [← hl] at hmono
  have hh : v = (0 : E3) := by simpa using hmono
  exact hv hh
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction HyperbolicCore
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece_2
end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.closedGeodesic_essential := @_root_.OAI.ThreeManifold.RiemannianCoordinates.closedGeodesic_essential
