-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:37:10.18528+00:00
-- url     : https://prove2.me/submissions/499b7d5b-cd2f-4495-a8ee-5aed5ea0a5bc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Coordinates.lean:L1100-L1148
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection_derivative. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_connection

-- ---- from OAI.Geometry.ConjugatePoints.Coordinates ----
namespace OAI

noncomputable section

/-!
# Riemannian coordinates, connections, curvature, and Jacobi fields.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

section MatrixSmooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : Type*} [Fintype n] [DecidableEq n] {R : X → Matrix n n ℝ} {x : X}
end MatrixSmooth

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

namespace CoordinateMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
lemma smoothAt {x : E3} (hx : x ∈ P.domain) : ContDiffAt ℝ ∞ f x :=
  P.smooth.contDiffAt (P.isOpen_domain.mem_nhds hx)
end CoordinateMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
lemma connection_derivative (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (t u v : E3) :
    let A := fderiv ℝ f x
    let H := fderiv ℝ (fderiv ℝ f) x
    let K := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
    K t u v + fderiv ℝ (connectionBilin h d) (f x) (A t) (A u) (A v) +
      connectionBilin h d (f x) (H t u) (A v) + connectionBilin h d (f x) (A u) (H t v) =
      H t (connectionBilin g c x u v) + A (fderiv ℝ (connectionBilin g c) x t u v) := by
  intro A H K
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let p : ℝ → E3 := fun s => x + s • t
  have hp : HasDerivAt p t 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const t).const_add x
  have hp0 : p 0 = x := by simp [p]
  have hs := P.smoothAt hx
  have hAs := hs.fderiv_right (m := ∞) (by simp)
  have hHs := hAs.fderiv_right (m := ∞) (by simp)
  have hdf : HasFDerivAt f A (p 0) := by
    rw [hp0]; exact (hs.differentiableAt (by simp)).hasFDerivAt
  have hdA : HasFDerivAt (fderiv ℝ f) H (p 0) := by
    rw [hp0]; exact (hAs.differentiableAt (by simp)).hasFDerivAt
  have hdH : HasFDerivAt (fderiv ℝ (fderiv ℝ f)) K (p 0) := by
    rw [hp0]; exact (hHs.differentiableAt (by simp)).hasFDerivAt
  have hdC : HasFDerivAt (connectionBilin g c) (fderiv ℝ (connectionBilin g c) x) (p 0) := by
    rw [hp0]; exact ((connectionBilin_smoothAt g hc (P.source hx)).differentiableAt (by simp)).hasFDerivAt
  have hdD : HasFDerivAt (connectionBilin h d) (fderiv ℝ (connectionBilin h d) (f x)) (f (p 0)) := by
    rw [hp0]; exact ((connectionBilin_smoothAt h hd (P.target hx)).differentiableAt (by simp)).hasFDerivAt
  have hf := hdf.comp_hasDerivAt 0 hp
  have hA := hdA.comp_hasDerivAt 0 hp
  have hH := hdH.comp_hasDerivAt 0 hp
  have hC := hdC.comp_hasDerivAt 0 hp
  have hD := hdD.comp_hasDerivAt 0 hf
  have hu := hA.clm_apply (hasDerivAt_const 0 u)
  have hv := hA.clm_apply (hasDerivAt_const 0 v)
  have hleft := ((hH.clm_apply (hasDerivAt_const 0 u)).clm_apply (hasDerivAt_const 0 v)).add
    ((hD.clm_apply hu).clm_apply hv)
  have hright := hA.clm_apply ((hC.clm_apply (hasDerivAt_const 0 u)).clm_apply (hasDerivAt_const 0 v))
  have he : (fun s => fderiv ℝ (fderiv ℝ f) (p s) u v +
      connectionBilin h d (f (p s)) (fderiv ℝ f (p s) u) (fderiv ℝ f (p s) v)) =ᶠ[𝓝 0]
      (fun s => fderiv ℝ f (p s) (connectionBilin g c (p s) u v)) := by
    filter_upwards [hp.continuousAt (hp0.symm ▸ P.isOpen_domain.mem_nhds hx)] with s hs'
    simp only [connectionBilin_apply]
    exact P.connection hc hd hs' u v
  have heq := hleft.unique (hright.congr_of_eventuallyEq he)
  simp only [map_zero,add_zero,Function.comp_apply,hp0,_root_.add_apply] at heq
  simpa only [A, add_assoc] using heq

end ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry

namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end LocalMetricIsometry
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_1
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_1
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_2
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_2
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_4
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_4
end ThreeManifold.RiemannianCoordinates

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection_derivative := @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection_derivative
