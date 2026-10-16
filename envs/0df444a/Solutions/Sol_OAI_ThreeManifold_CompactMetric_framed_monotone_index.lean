-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.framed_monotone_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:15:23.564842+00:00
-- url     : https://prove2.me/submissions/60550c4a-0c39-4ff6-b232-92d2399d95e7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L1157-L1229
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.framed_monotone_index. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Cometric_P_elliptic
import Theorems.Thm_OAI_ThreeManifold_Cometric_coordinateCometric_end_deriv
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_gauge_index_nonnegative
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_scalar_equation
import Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_enter_transverse

-- ---- from OAI.Geometry.ConjugatePoints.Neck ----
namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

lemma pairing_matrix_neg (A : TMat) (u v : TVec) :
    pairing (-A) u v = -pairing A u v := by
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

lemma matrix_mul_hasDerivAt {M N : ℝ → TMat} {M' N' : TMat} {s : ℝ}
    (hM : HasDerivAt M M' s) (hN : HasDerivAt N N' s) :
    HasDerivAt (fun r => M r * N r) (M' * N s + M s * N') s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h (k : Fin 2) (_hk : k ∈ Finset.univ) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hN k) j)
  convert! HasDerivAt.fun_sum h using 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

lemma inverse_first_jet {P Q : ℝ → TMat} {H A : TMat} {s : ℝ}
    (hP : HasDerivAt P H s) (hQ : HasDerivAt Q A s)
    (hPQ : ∀ᶠ r in nhds s, P r * Q r = 1) (hQP : Q s * P s = 1) :
    A = -Q s * H * Q s := by
  have hprod := matrix_mul_hasDerivAt hP hQ
  have heq : (fun _ : ℝ => (1 : TMat)) =ᶠ[nhds s] (fun r => P r * Q r) :=
    Filter.Eventually.mono hPQ (fun _ h => h.symm)
  have hzero : H * Q s + P s * A = 0 :=
    (hprod.congr_of_eventuallyEq heq).unique (hasDerivAt_const s (1 : TMat))
  have h := congrArg (fun N : TMat => Q s * N) hzero
  simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at h
  calc
    A = -(Q s * H * Q s) := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using h)
    _ = _ := by simp only [neg_mul]

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

lemma P_smooth (δ : ℝ) : ContDiff ℝ ∞ (P δ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [P] <;> fun_prop

lemma sqnorm_nonneg (p : V2) : 0 ≤ sqnorm p := by unfold sqnorm; positivity

lemma sqnorm_eq_zero_iff (p : V2) : sqnorm p = 0 ↔ p = 0 := by
  rw [sqnorm, add_eq_zero_iff_of_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]
  simp only [sq_eq_zero_iff, funext_iff, Fin.forall_fin_two, Pi.zero_apply]

lemma sqnorm_pos {p : V2} (hp : p ≠ 0) : 0 < sqnorm p :=
  (sqnorm_nonneg p).lt_of_ne' (mt (sqnorm_eq_zero_iff p).mp hp)

lemma shear_norm_upper (x y c : ℝ) (hc : |c| ≤ 1) :
    x ^ 2 + (y + c * x) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2) := by
  have hc' : c ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one c).mpr hc
  have hcx := mul_nonneg (sub_nonneg.mpr hc') (sq_nonneg x)
  nlinarith [sq_nonneg (y - c * x), sq_nonneg y]

lemma shear_norm_lower (x y c : ℝ) (hc : |c| ≤ 1) :
    (x ^ 2 + y ^ 2) / 3 ≤ x ^ 2 + (y + c * x) ^ 2 := by
  have h := shear_norm_upper x (y + c * x) (-c) (by simpa using hc)
  have he : y + c * x + -c * x = y := by ring
  rw [he] at h
  linarith

lemma P_hermitian (δ t : ℝ) : (P δ t).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma frame_inverse (δ : ℝ) : C₂ δ * T₂ δ = 1 ∧ T₂ δ * C₂ δ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [T₂, C₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma P_left_endpoint {δ τ : ℝ} (hτ : τ ≤ 1 / 4) :
    P δ τ = !![1 + δ * A τ, 0; 0, 1 + δ * A 1] := by
  have hc := χ_eq_zero (show τ ≤ 5 / 12 by linarith)
  have hA := A_plateau (show 2 / 3 ≤ 1 - τ by linarith) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, d₁, d₂, shear, hc, hA]

lemma P_right_endpoint {δ τ : ℝ} (hτ : τ ≤ 1 / 4) :
    PEnd δ τ = !![1 + δ * A τ, 0; 0, 1 + δ * A 1] := by
  have hc := χ_eq_one (show 7 / 12 ≤ 1 - τ by linarith)
  have hA := A_plateau (show 2 / 3 ≤ 1 - τ by linarith) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  have he : 1 - (1 - τ) = τ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PEnd, C₂, P, d₁, d₂, shear, hc, hA, he,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

lemma qform_congruence (C M : Mat2) (p : V2) :
    qform (C * M * Cᵀ) p = qform M (Cᵀ *ᵥ p) := by
  simp [qform, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma C₂_transpose (δ : ℝ) : (C₂ δ)ᵀ = C₂ δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma C₂_norm_bounds {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (p : V2) :
    sqnorm p / 3 ≤ sqnorm (C₂ δ *ᵥ p) ∧ sqnorm (C₂ δ *ᵥ p) ≤ 3 * sqnorm p := by
  have h : |-(δ ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg δ)]
    nlinarith [hδ.1, hδ.2]
  have hl := shear_norm_lower (p 1) (p 0) (-(δ ^ 2)) h
  have hu := shear_norm_upper (p 1) (p 0) (-(δ ^ 2)) h
  simp [sqnorm, C₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> nlinarith

lemma PEnd_elliptic {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) (p : V2) :
    sqnorm p / 9 ≤ qform (PEnd δ τ) p ∧ qform (PEnd δ τ) p ≤ 18 * sqnorm p := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hp := P_elliptic hδ ht (C₂ δ *ᵥ p)
  have hc := C₂_norm_bounds hδ p
  rw [PEnd, qform_congruence, C₂_transpose]
  constructor <;> linarith [hp.1, hp.2, hc.1, hc.2]

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Returning ----
namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.Turning

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

lemma coordinateCometric_smooth (right : Bool) (δ : ℝ) :
    ContDiff ℝ ∞ (coordinateCometric right δ) := by
  cases right
  · exact P_smooth δ
  · exact (congruenceCLM (C₂ δ)).contDiff.comp
      ((P_smooth δ).comp (contDiff_const.sub contDiff_id))

lemma coordinateCometric_transpose (right : Bool) (δ t : ℝ) :
    (coordinateCometric right δ t)ᵀ = coordinateCometric right δ t := by
  cases right
  · exact Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ t)
  · change (C₂ δ * P δ (1 - t) * (C₂ δ)ᵀ)ᵀ = C₂ δ * P δ (1 - t) * (C₂ δ)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ (1 - t)), Matrix.mul_assoc]

lemma coordinateCometric_end {right : Bool} {δ t : ℝ} (ht : t ≤ 1 / 4) :
    coordinateCometric right δ t = !![1 + δ * A t, 0; 0, 1 + δ * A 1] := by
  cases right
  · exact P_left_endpoint ht
  · exact P_right_endpoint ht

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

end

-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning

lemma coordinateCometric_posDef {right : Bool} {δ u : ℝ}
    (hbound : ∀ q, sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q) :
    (coordinateCometric right δ u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (coordinateCometric_transpose right δ u))
  intro q hq
  change 0 < qform (coordinateCometric right δ u) q
  have hs := sqnorm_pos hq
  have hh := hbound q
  linarith

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma contDiffAt_det_two {R : ℝ → TMat} {s : ℝ} (hR : ContDiffAt ℝ ∞ R s) :
    ContDiffAt ℝ ∞ (fun u => (R u).det) s := by
  simp only [Matrix.det_fin_two]
  exact ((contDiffAt_pi.mp (contDiffAt_pi.mp hR 0) 0).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hR 1) 1)).sub
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hR 0) 1).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hR 1) 0))

lemma matrix_inverse_first_deriv {R : ℝ → TMat} {s : ℝ}
    (hR : ContDiff ℝ ∞ R) (hdet : (R s).det ≠ 0) :
    deriv (fun u => (R u)⁻¹) s = -(R s)⁻¹ * deriv R s * (R s)⁻¹ := by
  apply inverse_first_jet ((hR.differentiable (by simp)).differentiableAt.hasDerivAt)
    ((matrix_inverse_smoothAt hR.contDiffAt hdet).differentiableAt (by simp)).hasDerivAt
  · filter_upwards [(contDiffAt_det_two hR.contDiffAt).continuousAt.eventually_ne hdet] with u hu
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu)
  · exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma metricInverse_transpose (right : Bool) (δ u : ℝ) :
    (metricInverse right δ u)ᵀ = metricInverse right δ u := by
  simp only [metricInverse, Matrix.transpose_nonsing_inv,
    coordinateCometric_transpose]

lemma metricInverse_first {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    deriv (metricInverse right δ) u =
      -metricInverse right δ u * deriv (coordinateCometric right δ) u * metricInverse right δ u :=
  matrix_inverse_first_deriv (coordinateCometric_smooth right δ) hdet

lemma metricInverse_endpoint {right : Bool} {δ : ℝ}
    (hdet : (coordinateCometric right δ 0).det ≠ 0) :
    metricInverse right δ 0 = !![1, 0; 0, (1 + δ * A 1)⁻¹] := by
  have hd : 1 + δ * A 1 ≠ 0 := by
    rw [coordinateCometric_end (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hdet
    simpa [Matrix.det_fin_two, A] using hdet
  unfold metricInverse
  apply Matrix.inv_eq_left_inv
  rw [coordinateCometric_end (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have ha : A 0 = 0 := by simp [A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]

lemma metricInverse_endpoint_deriv {right : Bool} {δ : ℝ}
    (hdet : (coordinateCometric right δ 0).det ≠ 0) :
    deriv (metricInverse right δ) 0 = !![-(δ * a 0), 0; 0, 0] := by
  rw [metricInverse_first hdet, metricInverse_endpoint hdet,
    coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

end

end OAI

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

lemma frame_elliptic (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) (q : TVec) :
    sqnorm q/9 ≤ qform (coordinateCometric right δ t) q ∧
      qform (coordinateCometric right δ t) q ≤ 18*sqnorm q := by
  cases right
  · have h := P_elliptic hδ ht q
    change sqnorm q/9 ≤ qform (P δ t) q ∧ qform (P δ t) q ≤ 18*sqnorm q
    constructor <;> linarith [h.1,h.2,sqnorm_nonneg q]
  · exact PEnd_elliptic hδ ht q
lemma frame_det_ne (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    (coordinateCometric right δ t).det ≠ 0 :=
  (coordinateCometric_posDef (fun q => (frame_elliptic right hδ ht q).1)).det_pos.ne'

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

lemma regularGauge_zero_germ {γ J : ℝ → E3} {s : ℝ} (hz : J =ᶠ[𝓝 s] 0) :
    regularGauge γ J =ᶠ[𝓝 s] 0 := by
  filter_upwards [hz] with r hr
  simp [regularGauge,hr]
lemma gaugeField_zero_germ {γ J : ℝ → E3} {s : ℝ} (hz : J =ᶠ[𝓝 s] 0) :
    gaugeField γ J =ᶠ[𝓝 s] 0 := by
  filter_upwards [hz,regularGauge_zero_germ (γ := γ) hz] with r hr hg
  simp [gaugeField,hr,hg]

lemma regular_gauge_neighborhood {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ ∞ γ U) (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ}
    (hsub : Icc a b ⊆ U)
    (hreg : ∀ s ∈ Icc a b, deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc a b ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (regularGauge γ J) V ∧ ∀ s ∈ V, gaugeField γ J s 0 = 0 := by
  let Z := interior {s | J s = 0}
  let D := U ∩ (fun s => deriv γ s 0) ⁻¹' {r : ℝ | r ≠ 0}
  have hv (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ (fun r => deriv γ r 0) s :=
    (contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt.comp s ((hγ.contDiffAt (hU.mem_nhds hs)).derivWithin (m := ∞) (by simp))
  have hD : IsOpen D := by
    apply (show ContinuousOn (fun s => deriv γ s 0) U from fun s hs => (hv s hs).continuousAt.continuousWithinAt).isOpen_inter_preimage hU
    exact isClosed_singleton.isOpen_compl
  let V := D ∪ (U ∩ Z)
  have hVU : V ⊆ U := by intro s hs; exact hs.elim And.left And.left
  have hsV (s : ℝ) (hs : s ∈ V) : deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0 := by
    rcases hs with hs | hs
    · exact Or.inl hs.2
    · exact Or.inr (mem_interior_iff_mem_nhds.mp hs.2)
  refine ⟨V,hD.union (hU.inter isOpen_interior),?_,hVU,?_,?_⟩
  · intro s hs
    rcases hreg s hs with hv | hz
    · exact Or.inl ⟨hsub hs,hv⟩
    · exact Or.inr ⟨hsub hs,mem_interior_iff_mem_nhds.mpr hz⟩
  · intro s hs
    apply ContDiffAt.contDiffWithinAt
    rcases hsV s hs with hn | hz
    · exact (((contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt.comp s
        (hJ.contDiffAt (hU.mem_nhds (hVU hs)))).neg.div (hv s (hVU hs)) hn)
    · exact contDiffAt_const.congr_of_eventuallyEq (regularGauge_zero_germ hz)
  · intro s hs
    rcases hsV s hs with hn | hz
    · dsimp [gaugeField,regularGauge]
      rw [div_mul_cancel₀ _ hn]
      ring
    · simpa using congrFun (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds 0
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

lemma force_end_nonnegative (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (p : TVec)
    {x : ℝ} (hx : x < 1/4) : 0 ≤ force right δ p x := by
  unfold force
  rw [coordinateCometric_end_deriv hx]
  have ha : 0 ≤ a x := a_nonneg x
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero]
  nlinarith [mul_nonneg (mul_nonneg hδ ha) (sq_nonneg (p 0))]

lemma neck_enter_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s) : 0 < v a :=
  scalar_enter_transverse hab (by norm_num : (0:ℝ) < 1/4) ht hv ha hpos
    (fun _ hx => force_end_nonnegative right hδ p hx)
end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

lemma coordinateCometric_flip (right : Bool) (δ t : ℝ) :
    coordinateCometric right δ t = flipFrame right δ * coordinateCometric (!right) δ (1-t) * (flipFrame right δ)ᵀ := by
  cases right with
  | true => simp [coordinateCometric,flipFrame,PEnd]
  | false =>
    simp only [coordinateCometric,flipFrame,Bool.false_eq_true,↓reduceIte,Bool.not_false]
    unfold PEnd
    rw [show 1-(1-t) = t by ring]
    simp only [← Matrix.mul_assoc,(frame_inverse δ).2,Matrix.one_mul]
    rw [Matrix.mul_assoc,← Matrix.transpose_mul,(frame_inverse δ).2,Matrix.transpose_one,Matrix.mul_one]

lemma coordinateCometric_flip_deriv (right : Bool) (δ t : ℝ) :
    deriv (coordinateCometric right δ) t = -(flipFrame right δ *
      deriv (coordinateCometric (!right) δ) (1-t) * (flipFrame right δ)ᵀ) := by
  have hd := ((coordinateCometric_smooth (!right) δ).differentiable (by simp) (1-t)).hasDerivAt.scomp t
    ((hasDerivAt_id t).const_sub 1)
  have he := (congruenceCLM (flipFrame right δ)).hasFDerivAt.comp_hasDerivAt t hd
  have hf : (fun r => (congruenceCLM (flipFrame right δ)) (coordinateCometric (!right) δ (1-r))) =
      coordinateCometric right δ := by
    funext r
    exact (coordinateCometric_flip right δ r).symm
  dsimp only [Function.comp_def] at he
  rw [hf] at he
  have he' := he.deriv
  change deriv (coordinateCometric right δ) t = flipFrame right δ * ((-1:ℝ) • deriv (coordinateCometric (!right) δ) (1-t)) * (flipFrame right δ)ᵀ at he'
  simpa only [zero_sub,neg_smul,one_smul,Matrix.mul_neg,Matrix.neg_mul] using he'

lemma force_far_end_nonpositive (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (p : TVec)
    {x : ℝ} (hx : 3/4 < x) : force right δ p x ≤ 0 := by
  unfold force
  rw [coordinateCometric_flip_deriv,pairing_matrix_neg]
  change -qform (flipFrame right δ * deriv (coordinateCometric (!right) δ) (1-x) * (flipFrame right δ)ᵀ) p ≤ 0
  rw [qform_congruence]
  have hh := PassageDynamics.force_end_nonnegative (!right) hδ ((flipFrame right δ)ᵀ *ᵥ p) (by linarith : 1-x < 1/4)
  unfold force at hh
  exact neg_nonpos.mpr hh

lemma inverse_jet_zero_nonpositive (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (coordinateCometric right δ 0).det ≠ 0) (z : TVec) :
    pairing (deriv (metricInverse right δ) 0) z z ≤ 0 := by
  rw [metricInverse_endpoint_deriv hd]
  have ha := a_nonneg (0:ℝ)
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero]
  nlinarith [mul_nonneg (mul_nonneg hδ ha) (sq_nonneg (z 0))]

lemma inverse_jet_one_nonnegative (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (coordinateCometric right δ 1).det ≠ 0) (z : TVec) :
    0 ≤ pairing (deriv (metricInverse right δ) 1) z z := by
  rw [metricInverse_first hd]
  simp only [Matrix.neg_mul,pairing_matrix_neg]
  have he := qform_congruence (metricInverse right δ 1) (deriv (coordinateCometric right δ) 1) z
  rw [metricInverse_transpose] at he
  change 0 ≤ -qform (metricInverse right δ 1 * deriv (coordinateCometric right δ) 1 * metricInverse right δ 1) z
  rw [he]
  exact neg_nonneg.mpr (force_far_end_nonpositive right hδ (metricInverse right δ 1 *ᵥ z) (x := 1) (by norm_num))

lemma zeroheight_boundary_nonnegative (right : Bool) {δ t v : ℝ} {u z : TVec}
    (hδ : 0 ≤ δ) (hd : (coordinateCometric right δ t).det ≠ 0)
    (ht : (t = 0 ∧ 0 ≤ v) ∨ (t = 1 ∧ v ≤ 0)) :
    0 ≤ boundaryTerm (deriv (metricInverse right δ) t) (v,u) (0,z) := by
  simp only [boundaryTerm,zero_mul,add_zero]
  rw [show -(1/2:ℝ)*v*pairing (deriv (metricInverse right δ) t) z z = -(v/2*pairing (deriv (metricInverse right δ) t) z z) by ring]
  rcases ht with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (inverse_jet_zero_nonpositive right hδ hd z))
  · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (inverse_jet_one_nonnegative right hδ hd z))

lemma zeroheight_boundary_nonpositive (right : Bool) {δ t v : ℝ} {u z : TVec}
    (hδ : 0 ≤ δ) (hd : (coordinateCometric right δ t).det ≠ 0)
    (ht : (t = 0 ∧ v ≤ 0) ∨ (t = 1 ∧ 0 ≤ v)) :
    boundaryTerm (deriv (metricInverse right δ) t) (v,u) (0,z) ≤ 0 := by
  simp only [boundaryTerm,zero_mul,add_zero]
  rw [show -(1/2:ℝ)*v*pairing (deriv (metricInverse right δ) t) z z = -(v/2*pairing (deriv (metricInverse right δ) t) z z) by ring]
  rcases ht with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos (by linarith) (inverse_jet_zero_nonpositive right hδ hd z))
  · exact neg_nonpos.mpr (mul_nonneg (by positivity) (inverse_jet_one_nonnegative right hδ hd z))
end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

lemma neck_enter_upper_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (ha : t a = 1) (hpos : ∀ s ∈ Ioo a b, t s < 1) : v a < 0 := by
  have hh := scalar_enter_transverse (t := fun s => 1-t s) (v := fun s => -v s)
    (F := fun x => -force right δ p (1-x)) hab (by norm_num : (0:ℝ) < 1/4)
    (fun s hs => by simpa using (ht s hs).const_sub 1)
    (fun s hs => by convert (hv s hs).neg using 1 <;> first | rfl | simp [neg_div])
    (by simp [ha]) (fun s hs => by linarith [hpos s hs])
    (fun x hx => neg_nonneg.mpr (force_far_end_nonpositive right hδ p (by linarith : 3/4 < 1-x)))
  linarith

lemma neck_exit_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (hr : ∀ s ∈ Ioo a b, t s ∈ Ioo (0:ℝ) 1) (hb : t b = 0 ∨ t b = 1) :
    (t b = 0 ∧ v b < 0) ∨ (t b = 1 ∧ 0 < v b) := by
  have href (s : ℝ) (hs : s ∈ Icc a b) : a+b-s ∈ Icc a b := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hdt (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun r => t (a+b-r)) (-v (a+b-s)) s := by
    convert (ht _ (href s hs)).comp s ((hasDerivAt_id s).const_sub (a+b)) using 1 <;> first | rfl | simp
  have hdv (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun r => -v (a+b-r)) (-force right δ p (t (a+b-s))/2) s := by
    convert ((hv _ (href s hs)).comp s ((hasDerivAt_id s).const_sub (a+b))).neg using 1 <;> first | rfl | simp [neg_div]
  rcases hb with hb | hb
  · left
    refine ⟨hb,?_⟩
    have hh := neck_enter_transverse right hδ hab hdt hdv (by simpa using hb)
      (fun s hs => (hr (a+b-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩).1)
    simpa using hh
  · right
    refine ⟨hb,?_⟩
    have hh := neck_enter_upper_transverse right hδ hab hdt hdv (by simpa using hb)
      (fun s hs => (hr (a+b-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩).2)
    simpa using hh
end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

theorem framed_monotone_index (right : Bool) {δ a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc a b, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (hrc : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo a b, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0)
    (hb : (γ b 0 = 0 ∨ γ b 0 = 1) ∨ J =ᶠ[𝓝 b] 0)
    (hn : ∀ s ∈ Ioo a b, deriv γ s 0 ≠ 0)
    (hunit : ∀ s ∈ Icc a b,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  have hgc (s : ℝ) (hs : s ∈ Icc a b) :=
    (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))
  have ht (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun r => γ r 0) (deriv γ s 0) s :=
    hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0
  have hv (s : ℝ) (hs : s ∈ Icc a b) :=
    framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs)
  have hentry : γ a 0 = 0 ∨ γ a 0 = 1 →
      (γ a 0 = 0 ∧ 0 < deriv γ a 0) ∨ (γ a 0 = 1 ∧ deriv γ a 0 < 0) := by
    rintro (hz | ho)
    · exact Or.inl ⟨hz,neck_enter_transverse right hδ.1.le hab ht hv hz (fun s hs => (hr s hs).1)⟩
    · exact Or.inr ⟨ho,neck_enter_upper_transverse right hδ.1.le hab ht hv ho (fun s hs => (hr s hs).2)⟩
  have hexit := neck_exit_transverse right hδ.1.le hab ht hv hr
  have hreg : ∀ s ∈ Icc a b, deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | has
    · rcases ha with ha | hz
      · rcases hentry ha with ⟨_,hv⟩ | ⟨_,hv⟩
        · exact Or.inl hv.ne'
        · exact Or.inl hv.ne
      · exact Or.inr hz
    rcases eq_or_lt_of_le hs.2 with rfl | hsb
    · rcases hb with hb | hz
      · rcases hexit hb with ⟨_,hv⟩ | ⟨_,hv⟩
        · exact Or.inl hv.ne
        · exact Or.inl hv.ne'
      · exact Or.inr hz
    exact Or.inl (hn s ⟨has,hsb⟩)
  obtain ⟨V,hV,hsubV,hVU,hgauge,hzero⟩ := regular_gauge_neighborhood hU
    (euclidean_curve_smooth hγ.1) (euclidean_field_smooth hU hγ.1 hJ) hsub hreg
  have hγV : IsGeodesicOn (framedNeck right hδ) γ V :=
    ⟨hγ.1.mono hVU,fun c hc s hs hsc => hγ.2 c hc s (hVU hs) hsc⟩
  apply framed_gauge_index_nonnegative right hδ hV hγV
    ((euclidean_field_smooth hU hγ.1 hJ).mono hVU) hgauge hzero hab.le hsubV hrc hunit
  let B (s : ℝ) := boundaryTerm (deriv (metricInverse right δ) (γ s 0))
    (splitVector (deriv γ s)) (splitVector (gaugeField γ J s))
  have hsplit (s : ℝ) (hs : s ∈ Icc a b) : splitVector (gaugeField γ J s) = (0,(splitVector (gaugeField γ J s)).2) := by
    apply Prod.ext
    · exact hzero s (hsubV hs)
    · rfl
  have hBa : 0 ≤ B a := by
    rcases ha with ha | hz
    · dsimp only [B]
      rw [hsplit a (left_mem_Icc.mpr hab.le)]
      apply zeroheight_boundary_nonnegative right hδ.1.le (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (hrc a (left_mem_Icc.mpr hab.le)))
      rcases hentry ha with ⟨ht,hv⟩ | ⟨ht,hv⟩
      · exact Or.inl ⟨ht,hv.le⟩
      · exact Or.inr ⟨ht,hv.le⟩
    · have hz' := (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds
      simp [B,hz',splitVector,boundaryTerm,pairing]
  have hBb : B b ≤ 0 := by
    rcases hb with hb | hz
    · dsimp only [B]
      rw [hsplit b (right_mem_Icc.mpr hab.le)]
      apply zeroheight_boundary_nonpositive right hδ.1.le (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (hrc b (right_mem_Icc.mpr hab.le)))
      rcases hexit hb with ⟨ht,hv⟩ | ⟨ht,hv⟩
      · exact Or.inl ⟨ht,hv.le⟩
      · exact Or.inr ⟨ht,hv.le⟩
    · have hz' := (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds
      simp [B,hz',splitVector,boundaryTerm,pairing]
  exact hBb.trans hBa
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
open OAI OAI.ThreeManifold OAI.ThreeManifold.CompactMetric
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.framed_monotone_index := @_root_.OAI.ThreeManifold.CompactMetric.framed_monotone_index
