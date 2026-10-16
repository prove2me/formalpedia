-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_index_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:17:30.858526+00:00
-- url     : https://prove2.me/submissions/3da05c0d-8220-481a-b03f-960710b22e73

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L1388-L1405
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_index_integral. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

-- ---- from OAI.Geometry.ConjugatePoints.Passages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Passage supports, extension, and compact metric estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X Y : Type} [TopologicalSpace X] (O : TopologicalSpace.Opens X) (e : O ≃ₜ O)
end ThreeManifold.TwoGluing
namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction GluedConstruction
end

section
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_2
end

open MetricConstruction CylinderConstruction GluedConstruction
end ThreeManifold.CompactMetric

namespace ThreeManifold.CylinderConstruction

section
open QuotientConstruction

end

attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder_1
end ThreeManifold.CylinderConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates Cometric Neck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_3
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.FinitePassage

end ThreeManifold.FinitePassage
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_4
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.PassageDynamics

end ThreeManifold.PassageDynamics

namespace ThreeManifold.SupportExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end ThreeManifold.SupportExtension
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck
lemma euclidean_curve_smooth {γ : ℝ → E3} {U : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) : ContDiffOn ℝ ∞ γ U :=
  contMDiffOn_iff_contDiffOn.mp hγ
lemma euclidean_fieldCoordinates (γ J : ℝ → E3) :
    fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) = J := by
  funext s
  change mfderiv I3 I3 (id : E3 → E3) (γ s) (J s) = J s
  rw [mfderiv_eq_fderiv,fderiv_id]
  rfl
lemma euclidean_field_smooth {γ J : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) : ContDiffOn ℝ ∞ J U := by
  intro s hs
  have h := smoothField_coordinatesAt hU hγ hJ (chart_mem_atlas E3 (0 : E3)) hs (mem_univ _)
  change ContDiffAt ℝ ∞ (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s at h
  rw [euclidean_fieldCoordinates] at h
  exact h.contDiffWithinAt

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

section
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients
end ThreeManifold.CompactMetric

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.NoConjugatePoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

lemma euclidean_covariant (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    covariantDerivative g γ J s = deriv J s + connectionTerm g (OpenPartialHomeomorph.refl E3)
      (γ s) (deriv γ s) (J s) := by
  unfold covariantDerivative
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma euclidean_curvature (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    curvatureAlong g γ J s = curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s)
      (J s) (deriv γ s) (deriv γ s) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma affine_hasDerivAt {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    HasDerivAt (fun r => f (a+k*r)) (k • deriv f (a+k*s)) s := by
  convert hf.hasDerivAt.scomp s (((hasDerivAt_id s).const_mul k).const_add a) using 1 <;> first | rfl | simp

lemma affine_deriv {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    deriv (fun r => f (a+k*r)) s = k • deriv f (a+k*s) := (affine_hasDerivAt hf).deriv

lemma connection_smul_left (g : SmoothMetric E3) (x u v : E3) (k : ℝ) :
    connectionTerm g (OpenPartialHomeomorph.refl E3) x (k • u) v =
      k • connectionTerm g (OpenPartialHomeomorph.refl E3) x u v := by
  simp only [← connectionBilin_apply,map_smul,_root_.smul_apply]
lemma euclidean_affine_covariant (g : SmoothMetric E3) {γ J : ℝ → E3} {s a k : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) (hJ : DifferentiableAt ℝ J (a+k*s)) :
    covariantDerivative g (fun r => γ (a+k*r)) (fun r => J (a+k*r)) s =
      k • covariantDerivative g γ J (a+k*s) := by
  rw [euclidean_covariant,euclidean_covariant,affine_deriv hγ,affine_deriv hJ,connection_smul_left]
  change (k • deriv J (a+k*s) + k • connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv γ (a+k*s)) (J (a+k*s)) : E3) = k • _
  exact (smul_add k _ _).symm

lemma curvature_smul_velocity (g : SmoothMetric E3) (x J T : E3) (k : ℝ) :
    curvatureTerm g (OpenPartialHomeomorph.refl E3) x J (k • T) (k • T) =
      (k*k) • curvatureTerm g (OpenPartialHomeomorph.refl E3) x J T T := by
  ext l
  simp only [curvatureTerm,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  ring

lemma euclidean_affine_index (g : SmoothMetric E3) {γ J : ℝ → E3} {s a k : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) (hJ : DifferentiableAt ℝ J (a+k*s)) :
    indexPairDensity g (fun r => γ (a+k*r)) (fun r => J (a+k*r)) (fun r => J (a+k*r)) s =
      k^2 * indexPairDensity g γ J J (a+k*s) := by
  unfold indexPairDensity
  rw [euclidean_affine_covariant g hγ hJ,euclidean_curvature,euclidean_curvature,
    affine_deriv hγ,curvature_smul_velocity]
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ (a+k*s))
  let D : E3 := covariantDerivative g γ J (a+k*s)
  change B (k • D) (k • D) -
    B ((k*k) • curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ (a+k*s)) (J (a+k*s))
      (deriv γ (a+k*s)) (deriv γ (a+k*s))) (J (a+k*s)) =
    k^2 * (B D D -
      B (curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ (a+k*s)) (J (a+k*s))
        (deriv γ (a+k*s)) (deriv γ (a+k*s))) (J (a+k*s)))
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_affine_index_integral (g : SmoothMetric E3) {γ J : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) {a k u v : ℝ} (hk : k ≠ 0)
    (hd : ∀ s ∈ uIcc u v, a+k*s ∈ U) :
    (∫ s in u..v, indexPairDensity g (fun r => γ (a+k*r))
      (fun r => J (a+k*r)) (fun r => J (a+k*r)) s) =
      k * ∫ s in (a+k*u)..(a+k*v), indexPairDensity g γ J J s := by
  calc
    _ = ∫ s in u..v, k^2 * indexPairDensity g γ J J (a+k*s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact euclidean_affine_index g
        (((euclidean_curve_smooth hγ).contDiffAt (hU.mem_nhds (hd s hs))).differentiableAt (by simp))
        (((euclidean_field_smooth hU hγ hJ).contDiffAt (hU.mem_nhds (hd s hs))).differentiableAt (by simp))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_mul _ hk a]
      simp only [smul_eq_mul]
      field_simp
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
open CompactMetric


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_index_integral := @_root_.OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_index_integral
