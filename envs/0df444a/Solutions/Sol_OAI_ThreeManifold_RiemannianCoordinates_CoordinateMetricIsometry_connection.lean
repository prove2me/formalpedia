-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:35:34.675692+00:00
-- url     : https://prove2.me/submissions/7bae2f53-28cf-4117-bb14-06b26f9d99eb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Coordinates.lean:L1061-L1090
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection. The node keeps its source
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
lemma metric_derivative (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (t u v : E3) :
    let A := fderiv ℝ f x
    let H := fderiv ℝ (fderiv ℝ f) x
    chartBilin g c x (connectionTerm g c x t u) v +
        chartBilin g c x u (connectionTerm g c x t v) =
      chartBilin h d (f x) (H t u + connectionTerm h d (f x) (A t) (A u)) (A v) +
        chartBilin h d (f x) (A u) (H t v + connectionTerm h d (f x) (A t) (A v)) := by
  intro A H
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let p : ℝ → E3 := fun s => x + s • t
  have hp : HasDerivAt p t 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const t).const_add x
  have hp0 : p 0 = x := by simp [p]
  have hs : ContDiffAt ℝ ∞ f x := P.smoothAt hx
  have hds : DifferentiableAt ℝ f x := hs.differentiableAt (by simp)
  have hAs : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdf : HasFDerivAt f A (p 0) := hp0.symm ▸ hds.hasFDerivAt
  have hdA : HasFDerivAt (fderiv ℝ f) H (p 0) := hp0.symm ▸ hAs.hasFDerivAt
  have hfp : HasDerivAt (f ∘ p) (A t) 0 := by
    exact hdf.comp_hasDerivAt 0 hp
  have hAu : HasDerivAt (fun s => fderiv ℝ f (p s) u) (H t u) 0 := by
    have h := (hdA.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const 0 u)
    convert h using 1 <;> first | rfl | simp only [map_zero,add_zero]
  have hAv : HasDerivAt (fun s => fderiv ℝ f (p s) v) (H t v) 0 := by
    have h := (hdA.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const 0 v)
    convert h using 1 <;> first | rfl | simp only [map_zero,add_zero]
  have hq1 := metric_fields_hasDerivAt g hc (show p 0 ∈ c.target by rw [hp0]; exact P.source hx) hp.differentiableAt
    (differentiableAt_const u) (differentiableAt_const v)
  have hq2 := metric_fields_hasDerivAt h hd (show (f ∘ p) 0 ∈ d.target by
    change f (p 0) ∈ d.target
    rw [hp0]
    exact P.target hx) hfp.differentiableAt
      hAu.differentiableAt hAv.differentiableAt
  have he : (fun s => chartBilin g c (p s) u v) =ᶠ[𝓝 0]
      (fun s => chartBilin h d (f (p s)) (fderiv ℝ f (p s) u) (fderiv ℝ f (p s) v)) := by
    have ho := hp.continuousAt (hp0.symm ▸ P.isOpen_domain.mem_nhds hx)
    filter_upwards [ho] with s hs'
    exact P.metric _ hs' u v
  have heq := hq1.unique (hq2.congr_of_eventuallyEq he)
  simpa only [alongDerivative,deriv_const,zero_add,hp.deriv,hfp.deriv,hAu.deriv,hAv.deriv,
    Function.comp_apply,hp0] using heq

lemma connection (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (u v : E3) :
    fderiv ℝ (fderiv ℝ f) x u v +
        connectionTerm h d (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) =
      fderiv ℝ f x (connectionTerm g c x u v) := by
  let A := fderiv ℝ f x
  let H := fderiv ℝ (fderiv ℝ f) x
  let q := chartBilin h d (f x)
  let B := fun u v => H u v + connectionTerm h d (f x) (A u) (A v) - A (connectionTerm g c x u v)
  have hBs : ∀ u v, B u v = B v u := by
    intro u v
    have hH := ((P.smoothAt hx).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq u v
    simp only [B,H,hH,connectionTerm_symm h d (f x) (A u) (A v),
      connectionTerm_symm g c x u v]
  have hBq : ∀ t u v, q (B t u) (A v) + q (A u) (B t v) = 0 := by
    intro t u v
    have he := P.metric_derivative hc hd hx t u v
    rw [P.metric x hx (connectionTerm g c x t u) v,
      P.metric x hx u (connectionTerm g c x t v)] at he
    change q (A (connectionTerm g c x t u)) (A v) +
      q (A u) (A (connectionTerm g c x t v)) =
        q (H t u + connectionTerm h d (f x) (A t) (A u)) (A v) +
        q (A u) (H t v + connectionTerm h d (f x) (A t) (A v)) at he
    dsimp only [B]
    simp only [map_sub,_root_.sub_apply]
    linarith
  have hz := symmetric_skew_difference_zero (fun u v => q u v)
    (chartBilin_symm h d (f x)) (fun _ hu => chartBilin_pos h hd (P.target hx) hu)
    (P.surjective x hx) hBs hBq u v
  exact sub_eq_zero.mp hz
end CoordinateMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
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


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection := @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection
