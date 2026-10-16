-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.realCompactMetric_nonnegative_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:24:42.529024+00:00
-- url     : https://prove2.me/submissions/1bf41b7b-22f3-4b81-bb1f-580615ed31ba

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L1579-L1625
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.realCompactMetric_nonnegative_index. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_height_boundary
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_index
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_neighborhood
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_neckPosition_mem_iff
import Theorems.Thm_OAI_ThreeManifold_FinitePassage_bounded_component
import Theorems.Thm_OAI_ThreeManifold_FinitePassage_endpoint_alternative
import Theorems.Thm_OAI_ThreeManifold_GlobalAssembly_integral_nonneg_of_passages
import Theorems.Thm_OAI_ThreeManifold_Neck_curvatureTerm_product
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_curvature
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_coordinate_derivative
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_covariantDerivative_map
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_mapField_smooth
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_nonpositiveAt
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_nonpositiveAt_image
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_unmapField_smooth
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_geodesic_of_acceleration_zero
import Theorems.Thm_OAI_ThreeManifold_WarpedCurvature_warpedModel_matrix

-- ---- from OAI.Geometry.ConjugatePoints.Cometric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Radial profiles, cometrics, and collar estimates.
-/

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.RadialProfile

lemma coordinate_strictMono {L : ℝ} (hL : 4 ≤ L) : StrictMono (coordinate L) := by
  apply strictMono_of_deriv_pos
  intro r
  rw [(coordinate_deriv L r).deriv]
  exact slope_pos hL r

end ThreeManifold.RadialProfile
end

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric

lemma a_pos {u : ℝ} (hu : u < 2 / 3) : 0 < a u :=
  expNegInvGlue.pos_of_pos (by linarith)

lemma a_hasDerivAt (u : ℝ) :
    HasDerivAt a (-a u / (2 / 3 - u) ^ 2) u := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (2 / 3 - u)
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] at h
  have hcomp := h.comp u ((hasDerivAt_const u (2 / 3)).sub (hasDerivAt_id u))
  convert! hcomp using 1
  simp [a, div_eq_mul_inv, inv_pow, mul_comm]

lemma a_deriv (u : ℝ) : deriv a u = -a u / (2 / 3 - u) ^ 2 :=
  (a_hasDerivAt u).deriv

lemma a_deriv_nonpos (u : ℝ) : deriv a u ≤ 0 := by
  rw [a_deriv]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (a_nonneg u)) (sq_nonneg _)

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

lemma lam_nonneg (t : ℝ) : 0 ≤ lam t := Real.smoothTransition.nonneg _
lemma lam_le_one (t : ℝ) : lam t ≤ 1 := Real.smoothTransition.le_one _
lemma lam_monotone : Monotone lam := fun _ _ h => Real.smoothTransition.monotone (by linarith)
lemma rate_pos {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    0 < rate δ t :=
  div_pos (mul_pos hδ.1 (a_pos (by linarith [ht.2])))
    (mul_pos (by norm_num) (denom_pos ⟨hδ.1.le, hδ.2⟩ ht.1))
lemma rate_le_delta {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    rate δ t ≤ δ := by
  apply (div_le_iff₀ (mul_pos (by norm_num) (denom_pos hδ ht))).mpr
  have h := denom_lower hδ ht
  have ha := mul_le_mul_of_nonneg_left (a_lt_one t).le hδ.1
  nlinarith [mul_nonneg hδ.1 (show 0 ≤ 2 * denom δ t - 1 by linarith)]
lemma k_positive {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    0 < k δ t := by
  have hr := rate_pos hδ ht
  have hl := lam_nonneg t
  have hu := lam_le_one t
  by_cases hl0 : lam t = 0
  · simp [k, hl0]
  · have hp := mul_pos (lt_of_le_of_ne hl (Ne.symm hl0)) hr
    dsimp [k]; linarith
lemma rate_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    HasDerivAt (rate δ)
      (δ * (deriv a t * denom δ t - δ * a t ^ 2) / (2 * denom δ t ^ 2)) t := by
  have hd : denom δ t ≠ 0 := ne_of_gt (denom_pos hδ ht)
  convert! (((a_hasDerivAt t).const_mul δ).div
    ((denom_hasDerivAt δ t).const_mul 2) (mul_ne_zero (by norm_num) hd)) using 1
  rw [← (a_hasDerivAt t).deriv]
  field_simp
lemma rate_deriv_neg {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    deriv (rate δ) t < 0 := by
  rw [(rate_hasDerivAt ⟨hδ.1.le, hδ.2⟩ ht.1).deriv]
  have hD := denom_pos ⟨hδ.1.le, hδ.2⟩ ht.1
  apply div_neg_of_neg_of_pos _ (mul_pos (by norm_num) (sq_pos_of_pos hD))
  apply mul_neg_of_pos_of_neg hδ.1
  have h1 := mul_nonpos_of_nonpos_of_nonneg (a_deriv_nonpos t) hD.le
  have h2 := mul_pos hδ.1 (sq_pos_of_pos (a_pos (u := t) (by linarith [ht.2])))
  linarith
lemma k_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    HasDerivAt (k δ) (deriv lam t * (rate δ t - 1) + lam t * deriv (rate δ) t) t := by
  by_cases ht : t < -3 / 4
  · have he : k δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using k_eq_one hu.le
    have hl : lam =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using lam_zero hu.le
    rw [hl.deriv_eq, deriv_const, lam_zero ht.le]
    simpa using (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he
  · have ht' : -1 ≤ t := by linarith
    have hl := lam_smooth.differentiable (by simp) t
    have hr := (rate_contDiffAt hδ ht').differentiableAt (by simp)
    convert! (hl.hasDerivAt.const_sub 1).add (hl.hasDerivAt.mul hr.hasDerivAt) using 1
    ring
lemma k_deriv_nonpos {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    deriv (k δ) t ≤ 0 := by
  rw [(k_hasDerivAt (t := t) ⟨hδ.1.le, hδ.2⟩).deriv]
  apply add_nonpos
  · apply mul_nonpos_of_nonneg_of_nonpos lam_monotone.deriv_nonneg
    have h := rate_le_delta ⟨hδ.1.le, hδ.2⟩ ht.1
    linarith [hδ.2]
  · exact mul_nonpos_of_nonneg_of_nonpos (lam_nonneg t) (rate_deriv_neg hδ ht).le
lemma ell_deriv {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    deriv (ell δ) = fun t => -k δ t * ell δ t :=
  funext fun _ => (ell_hasDerivAt hδ).deriv
lemma ell_second {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    deriv (deriv (ell δ)) t = (k δ t ^ 2 - deriv (k δ) t) * ell δ t := by
  rw [ell_deriv hδ]
  have hk := ((k_smooth hδ).differentiable (by simp) t).hasDerivAt
  convert! (hk.neg.mul (ell_hasDerivAt hδ)).deriv using 1
  dsimp
  ring
lemma ell_strictConvex_second {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2))
    (ht : t ∈ Icc (-1) 0) : 0 < deriv (deriv (ell δ)) t := by
  rw [ell_second ⟨hδ.1.le, hδ.2⟩]
  apply mul_pos _ (ell_pos δ t)
  have h1 := k_deriv_nonpos hδ ht
  have h2 := sq_pos_of_pos (k_positive hδ ht)
  linarith

end ThreeManifold.Collar

end

end OAI

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

lemma pairing_add_right (A : TMat) (u v w : TVec) :
    pairing A u (v + w) = pairing A u v + pairing A u w := by
  simp only [pairing, Matrix.mulVec_add, dotProduct_add]
lemma pairing_sub_left (A : TMat) (u v w : TVec) :
    pairing A (u - v) w = pairing A u w - pairing A v w := by
  simp only [pairing, sub_dotProduct]
lemma pairing_sub_right (A : TMat) (u v w : TVec) :
    pairing A u (v - w) = pairing A u v - pairing A u w := by
  simp only [pairing, Matrix.mulVec_sub, dotProduct_sub]
lemma pairing_smul_left (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A (r • u) v = r * pairing A u v := by
  simp only [pairing, smul_dotProduct, smul_eq_mul]
lemma pairing_smul_right (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A u (r • v) = r * pairing A u v := by
  simp only [pairing, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma pairing_matrix_sub (A B : TMat) (u v : TVec) :
    pairing (A - B) u v = pairing A u v - pairing B u v := by
  simp only [pairing, Matrix.sub_mulVec, dotProduct_sub]
lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

lemma metric_add_right (Q : TMat) (U V W : Vec) :
    metric Q U (V + W) = metric Q U V + metric Q U W := by
  simp only [metric, Prod.fst_add, Prod.snd_add, pairing_add_right]
  ring
lemma metric_sub_right (Q : TMat) (U V W : Vec) :
    metric Q U (V - W) = metric Q U V - metric Q U W := by
  simp only [metric, Prod.fst_sub, Prod.snd_sub, pairing_sub_right]
  ring
lemma metric_smul_right (Q : TMat) (r : ℝ) (U V : Vec) :
    metric Q U (r • V) = r * metric Q U V := by
  simp only [metric, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pairing_smul_right]
  ring
lemma metric_symm {Q : TMat} (hQ : Qᵀ = Q) (U V : Vec) :
    metric Q U V = metric Q V U := by
  rw [metric, metric, pairing_symm hQ]
  ring

lemma pairing_inverse {P Q : TMat} (hQP : Q * P = 1) (u v : TVec) :
    pairing Q u (P *ᵥ v) = dotProduct u v := by
  simp only [pairing, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]

lemma metric_gamma {P Q : TMat} (hQP : Q * P = 1) (A : TMat) (U V W : Vec) :
    metric Q U (gamma P A V W) =
      -(1 / 2 : ℝ) * U.1 * pairing A V.2 W.2 +
       (1 / 2 : ℝ) * V.1 * pairing A U.2 W.2 +
       (1 / 2 : ℝ) * W.1 * pairing A U.2 V.2 := by
  simp only [metric, gamma, pairing_smul_right, pairing_add_right,
    pairing_inverse hQP]
  simp only [pairing]
  ring

lemma metric_gammaPrime {P Q : TMat} (hQP : Q * P = 1) (A B : TMat) (U V W : Vec) :
    metric Q U (gammaPrime P A B V W) =
      -(1 / 2 : ℝ) * U.1 * pairing B V.2 W.2 +
       (1 / 2 : ℝ) * V.1 * pairing (B - A * P * A) U.2 W.2 +
       (1 / 2 : ℝ) * W.1 * pairing (B - A * P * A) U.2 V.2 := by
  have h (v : TVec) : Q *ᵥ ((P * B - P * A * P * A) *ᵥ v) =
      (B - A * P * A) *ᵥ v := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul]
  simp only [metric, gammaPrime, pairing_smul_right, pairing_add_right]
  simp only [pairing, h]
  ring

lemma sandwich_transpose {P A : TMat} (hP : Pᵀ = P) (hA : Aᵀ = A) :
    (A * P * A)ᵀ = A * P * A := by
  simp only [Matrix.transpose_mul, hA, hP, Matrix.mul_assoc]

lemma pairing_sandwich (P A : TMat) (u v : TVec) :
    pairing A u (P *ᵥ (A *ᵥ v)) = pairing (A * P * A) u v := by
  simp only [pairing, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma curvature_contraction {P Q A B : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B) (V T : Vec) :
    metric Q V (curvatureJet P A B V T T) =
      -(1 / 2 : ℝ) * pairing B (V.1 • T.2 - T.1 • V.2) (V.1 • T.2 - T.1 • V.2) +
       (1 / 4 : ℝ) * pairing (A * P * A)
         (V.1 • T.2 - T.1 • V.2) (V.1 • T.2 - T.1 • V.2) +
       (1 / 4 : ℝ) * ((pairing A V.2 T.2) ^ 2 -
         pairing A V.2 V.2 * pairing A T.2 T.2) := by
  have hS := sandwich_transpose hP hA
  simp only [curvatureJet, metric_sub_right, metric_add_right, metric_smul_right,
    metric_gammaPrime hQP, metric_gamma hQP]
  dsimp only [gamma]
  simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
    pairing_add_right, pairing_sandwich, pairing_matrix_sub,
    pairing_symm hB T.2 V.2,
    pairing_symm hS T.2 V.2]
  ring

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

lemma split_join (u : Vec) : splitVector (joinVector u) = u := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

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

-- ---- from OAI.Geometry.ConjugatePoints.Curvature ----
namespace OAI

noncomputable section

/-!
# Local isometries, warped curvature, and compact curvature estimates.
-/

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
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

lemma mapField_coordinates {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hp : γ s ∈ P.domain) (hpc : γ s ∈ c.source) (hpd : f (γ s) ∈ d.source) :
    fieldCoordinates (f ∘ γ) (P.mapField γ J) d s =
      fderiv ℝ (d ∘ f ∘ c.symm) (c (γ s)) (fieldCoordinates γ J c s) :=
  P.coordinate_derivative hc hd hp hpc hpd (J s)

lemma comp_smooth {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain) :
    ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ (f ∘ γ) U := by
  intro s hs
  exact ((P.smoothAt (hγP hs)).comp s (hγ.contMDiffAt (hU.mem_nhds hs))).contMDiffWithinAt

lemma coordinateDomain_mem {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    {p : M} (hp : p ∈ P.domain) (hpc : p ∈ c.source) (hpd : f p ∈ d.source) :
    c p ∈ P.coordinateDomain c d := by
  refine ⟨⟨c.map_source hpc,?_⟩,?_⟩
  · change c.symm (c p) ∈ P.domain
    rw [c.left_inv hpc]; exact hp
  · change f (c.symm (c p)) ∈ d.source
    rw [c.left_inv hpc]; exact hpd

lemma velocity_map {γ : ℝ → M} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hp : γ s ∈ P.domain) :
    velocity (f ∘ γ) s = mfderiv I3 I3 f (γ s) (velocity γ s) := by
  have he := mfderiv_comp s ((P.smoothAt hp).mdifferentiableAt (by simp))
    (hγ.mdifferentiableAt (by simp))
  exact congrArg (fun L => L 1) he

lemma curvatureAlong_map {γ : ℝ → M} (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hp : γ s ∈ P.domain) :
    curvatureAlong h (f ∘ γ) (P.mapField γ J) s =
      mfderiv I3 I3 f (γ s) (curvatureAlong g γ J s) := by
  let c := chartAt E3 (γ s)
  let d := chartAt E3 (f (γ s))
  have hc := chart_mem_atlas E3 (γ s)
  have hd := chart_mem_atlas E3 (f (γ s))
  have hpc := mem_chart_source E3 (γ s)
  have hpd := mem_chart_source E3 (f (γ s))
  have hy := (P.smoothAt hp).comp s hγ
  apply (mdifferentiable_of_mem_atlas (I := I3) hd).mfderiv_injective hpd
  change fieldCoordinates (f ∘ γ) (curvatureAlong h (f ∘ γ) (P.mapField γ J)) d s =
    fieldCoordinates (f ∘ γ) (P.mapField γ (curvatureAlong g γ J)) d s
  rw [curvatureAlong_coordinates h (P.mapField γ J) hy hd hpd,
    P.mapField_coordinates hc hd J hp hpc hpd,
    P.mapField_coordinates hc hd (curvatureAlong g γ J) hp hpc hpd,
    curvatureAlong_coordinates g J hγ hc hpc]
  have hv : deriv (d ∘ (f ∘ γ)) s =
      fderiv ℝ (d ∘ f ∘ c.symm) (c (γ s)) (deriv (c ∘ γ) s) := by
    rw [← velocity_coordinates hy hd hpd,← velocity_coordinates hγ hc hpc]
    change mfderiv I3 I3 d (f (γ s)) (velocity (f ∘ γ) s) = _
    rw [P.velocity_map hγ hp]
    exact P.coordinate_derivative hc hd hp hpc hpd _
  rw [hv]
  have he := (P.coordinates hc hd).curvature hc hd
    (P.coordinateDomain_mem hp hpc hpd) (fieldCoordinates γ J c s)
      (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)
  dsimp only at he
  have hp' : (d ∘ f ∘ c.symm) (c (γ s)) = d (f (γ s)) := by
    simp only [Function.comp_apply,c.left_inv hpc]
  rw [hp'] at he
  exact he

lemma indexPairDensity_map {γ : ℝ → M} {J K : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn γ J U) (hK : SmoothFieldOn γ K U) {s : ℝ} (hs : s ∈ U) :
    indexPairDensity h (f ∘ γ) (P.mapField γ J) (P.mapField γ K) s =
      indexPairDensity g γ J K s := by
  unfold indexPairDensity
  rw [P.covariantDerivative_map hU hγ hγP hJ hs,
    P.covariantDerivative_map hU hγ hγP hK hs,
    P.curvatureAlong_map J (hγ.contMDiffAt (hU.mem_nhds hs)) (hγP hs)]
  exact congrArg₂ (· - ·)
    (P.metric _ (hγP hs) (covariantDerivative g γ J s) (covariantDerivative g γ K s)).symm
    (P.metric _ (hγP hs) (curvatureAlong g γ J s) (K s)).symm
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
lemma covariantDerivative_germ (g : SmoothMetric M) {γ : ℝ → M}
    {J K : ∀ s, TangentSpace I3 (γ s)} {s : ℝ} (he : J =ᶠ[𝓝 s] K) :
    covariantDerivative g γ J s = covariantDerivative g γ K s := by
  simp only [covariantDerivative]
  congr 1
  apply along_congr g _ Filter.EventuallyEq.rfl
  filter_upwards [he] with r hr
  unfold fieldCoordinates
  rw [hr]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
lemma geodesic_map {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn g γ U) (hγP : MapsTo γ U P.domain) :
    IsGeodesicOn h (f ∘ γ) U := by
  apply geodesic_of_acceleration_zero h hU (P.comp_smooth hU hγ.1 hγP)
  intro s hs
  have he : velocity (f ∘ γ) =ᶠ[𝓝 s] P.mapField γ (velocity γ) := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact P.velocity_map (hγ.1.contMDiffAt (hU.mem_nhds hr)) (hγP hr)
  rw [covariantDerivative_germ h he,
    P.covariantDerivative_map hU hγ.1 hγP (velocity_smooth hU hγ.1) hs,
    geodesic_acceleration_zero g hU hγ hs,map_zero]
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.WarpedCurvature
open Neck RiemannianCoordinates

lemma diag_transpose (a b : ℝ) : (diag a b)ᵀ = diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
lemma diag_mul (a b c d : ℝ) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,Matrix.mul_apply,Fin.sum_univ_two]
lemma diag_pairing (a b : ℝ) (u v : TVec) : pairing (diag a b) u v = a*u 0*v 0+b*u 1*v 1 := by
  simp [pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,diag]
  ring
lemma diag_deriv {a b : ℝ → ℝ} {a' b' s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun t => diag (a t) (b t)) (diag a' b') s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hb

lemma QP (r : ℝ → ℝ) {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0) :
    Q r c t * P r c t = 1 := by
  rw [Q,P,diag_mul]
  simp only [mul_inv_cancel₀ (pow_ne_zero 2 hr),mul_inv_cancel₀ (pow_ne_zero 2 hc)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [diag]
lemma PQ (r : ℝ → ℝ) {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0) :
    P r c t * Q r c t = 1 := by
  rw [P,Q,diag_mul]
  simp only [inv_mul_cancel₀ (pow_ne_zero 2 hr),inv_mul_cancel₀ (pow_ne_zero 2 hc)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [diag]
lemma Q_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (c t : ℝ) : HasDerivAt (Q r c) (A r t) t := by
  change HasDerivAt (fun s => diag ((r s)^2) (c^2)) (diag (2*r t*deriv r t) 0) t
  simpa only [Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one] using diag_deriv (((hs.differentiable (by simp)) t).hasDerivAt.pow 2) (hasDerivAt_const t (c^2))
lemma A_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (t : ℝ) : HasDerivAt (A r) (B r t) t := by
  have h := (((hs.differentiable (by simp)) t).hasDerivAt.const_mul 2).mul
    ((((contDiff_infty_iff_deriv.mp hs).2).differentiable (by simp) t).hasDerivAt)
  convert diag_deriv h (hasDerivAt_const t (0:ℝ)) using 1
  · rfl
  · simp only [B]
    congr 1
    ring
lemma P_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (hr : ∀ t, r t ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (P r c) (-P r c t * A r t * P r c t) t := by
  have hd := diag_deriv ((((hs.differentiable (by simp)) t).hasDerivAt.pow 2).inv (pow_ne_zero 2 (hr t)))
    (hasDerivAt_const t ((c^2)⁻¹))
  have he := inverse_first_jet (Q_deriv hs c t) hd
    (Filter.Eventually.of_forall (fun s => QP r (hr s) hc)) (PQ r (hr t) hc)
  rw [he] at hd
  exact hd

lemma curvature_scalar {r : ℝ → ℝ} {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0)
    (V T : Vec) :
    metric (Q r c t) V (curvatureJet (P r c t) (A r t) (B r t) V T T) =
      -(r t * deriv (deriv r) t) * (V.1*T.2 0-T.1*V.2 0)^2 := by
  have hP : (P r c t)ᵀ = P r c t := diag_transpose _ _
  have hA : (A r t)ᵀ = A r t := diag_transpose _ _
  have hB : (B r t)ᵀ = B r t := diag_transpose _ _
  rw [curvature_contraction (QP r hr hc) hP hA hB]
  simp only [P,A,B,diag_mul,diag_pairing,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    zero_mul,add_zero]
  field_simp [hr]
  ring

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
lemma metric_of_block (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) {x : E3} {Q : TMat}
    (he : metricMatrix g c x = blockMatrix Q) (u v : E3) :
    chartBilin g c x u v = metric Q (splitVector u) (splitVector v) := by
  rw [← bilin_matrix]
  change ∑ i, ∑ j, metricMatrix g c x i j * u i * v j = _
  rw [he]
  simp [blockMatrix,metric,splitVector,pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_three,Fin.sum_univ_two]
  ring

lemma warped_curvature (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (hr : ∀ t, r t ≠ 0) {b : ℝ} (hb : b ≠ 0)
    {x : E3} (hg : metricMatrix g c =ᶠ[𝓝 x] fun y => blockMatrix (Q r b (y 0))) (u v : E3) :
    chartBilin g c x (curvatureTerm g c x u v v) u =
      -(r (x 0)*deriv (deriv r) (x 0))*(u 0*v 1-v 0*u 1)^2 := by
  have hj : ∀ᶠ t in 𝓝 (x 0), HasDerivAt (Q r b) (A r t) t ∧ Q r b t * P r b t = 1 ∧ (A r t)ᵀ = A r t :=
    Filter.Eventually.of_forall (fun t => ⟨Q_deriv hs b t,QP r (hr t) hb,diag_transpose _ _⟩)
  rw [curvatureTerm_product g c hg hj (P_deriv hs hr hb (x 0)) (A_deriv hs (x 0)),
    metric_of_block g c hg.eq_of_nhds,split_join,metric_symm (show (Q r b (x 0))ᵀ = Q r b (x 0) from diag_transpose _ _),curvature_scalar (hr (x 0)) hb]
  rfl
lemma warped_nonpositive (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (hr : ∀ t, 0 < r t) {b : ℝ} (hb : b ≠ 0)
    {x : E3} (hg : metricMatrix g c =ᶠ[𝓝 x] fun y => blockMatrix (Q r b (y 0)))
    (hconv : 0 ≤ deriv (deriv r) (x 0)) (u v : E3) :
    chartBilin g c x (curvatureTerm g c x u v v) u ≤ 0 := by
  rw [warped_curvature g c hs (fun t => (hr t).ne') hb hg]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (hr _).le hconv)) (sq_nonneg _)
end ThreeManifold.WarpedCurvature
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
end ThreeManifold.Rechart

namespace ThreeManifold.CylinderConstruction
open MetricConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder
variable {r s c : ℝ → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ t, r t ≠ 0) (hs : ∀ t, s t ≠ 0)
end ThreeManifold.CylinderConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
lemma nonpositiveAt_of_chart (g : SmoothMetric M) {p : M}
    {d : OpenPartialHomeomorph M E3} (hd : d ∈ atlas E3 M) (hpd : p ∈ d.source)
    (hn : ∀ u v : E3, chartBilin g d (d p) (curvatureTerm g d (d p) u v v) u ≤ 0) :
    NonpositiveAt g p := by
  intro c hc hpc u v
  have hp : c.symm (c p) ∈ d.source := by rw [c.left_inv hpc]; exact hpd
  have he := chart_metric_transform g hc hd (c.map_source hpc) hp
    (curvatureTerm g c (c p) u v v) u
  have hR := curvature_change g hc hd (c.map_source hpc) hp u v v
  dsimp only at hR
  rw [← hR] at he
  simp only [Function.comp_apply,c.left_inv hpc] at he
  rw [he]
  exact hn _ _

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.WarpedCurvature
open MetricConstruction CylinderConstruction RiemannianCoordinates
variable {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0)
lemma warpedModel_nonpositiveAt (x : E3) (hpos : 0 < r (x 0))
    (hc : 0 ≤ deriv (deriv r) (x 0)) : NonpositiveAt (warpedModel hs hb hr) x := by
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  rw [warped_curvature _ _ hs hr hb (Filter.Eventually.of_forall (warpedModel_matrix hs hb hr))]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hpos.le hc)) (sq_nonneg _)
end ThreeManifold.WarpedCurvature

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature
lemma ell_convex_left {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : t ≤ 0) :
    0 < deriv (deriv (Collar.ell δ)) t := by
  by_cases h : -1 ≤ t
  · exact Collar.ell_strictConvex_second hδ ⟨h,ht⟩
  · have he : Collar.k δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds (show t < -3/4 by linarith)] with s hs
      exact Collar.k_eq_one hs.le
    rw [Collar.ell_second ⟨hδ.1.le,hδ.2⟩,he.eq_of_nhds,he.deriv_eq,deriv_const]
    simpa using Collar.ell_pos δ t
lemma radius₁_convex_left {δ B t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) (ht : t ≤ 0) :
    0 < deriv (deriv (radius₁ δ B)) t := by
  change 0 < deriv (deriv (fun s => (δ^2*B/6)*Collar.ell δ s)) t
  rw [deriv_const_mul_field',deriv_const_mul_field]
  exact mul_pos (div_pos (mul_pos (sq_pos_of_pos hδ.1) hB) (by norm_num)) (ell_convex_left hδ ht)

lemma neckModel_matrix_left {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {x : E3} (hx : x 0 < 1/3) :
    metricMatrix (neckModel hδ hB) (OpenPartialHomeomorph.refl E3) x =
      Neck.blockMatrix (Q (radius₁ δ B) (B/6*Collar.ell δ 1) (x 0)) := by
  ext i j
  change (neckModel hδ hB).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change (neckModel hδ hB).inner x (basisVector i) (basisVector j) = _
  rw [neckModel_apply,Cometric.χ_eq_zero (by linarith : x 0 ≤ 5/12)]
  have hr : radius₂ δ B (x 0) = B/6*Collar.ell δ 1 := by
    rw [radius₂,ell_plateau ⟨hδ.1.le,hδ.2⟩ (by linarith)]
  rw [hr]
  fin_cases i <;> fin_cases j <;> simp [Q,WarpedCurvature.diag,Neck.blockMatrix,basisVector]
lemma neckModel_nonpositive_left {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {x : E3} (hx : x 0 ≤ 0) : NonpositiveAt (neckModel hδ hB) x := by
  have hb : B/6*Collar.ell δ 1 ≠ 0 := (mul_pos (div_pos hB (by norm_num)) (Collar.ell_pos _ _)).ne'
  have he : metricMatrix (neckModel hδ hB) (OpenPartialHomeomorph.refl E3) =ᶠ[𝓝 x]
      fun y => Neck.blockMatrix (Q (radius₁ δ B) (B/6*Collar.ell δ 1) (y 0)) := by
    filter_upwards [((continuous_apply 0).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (show x 0 < 1/3 by linarith)))] with y hy
    exact neckModel_matrix_left hδ hB hy
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  exact warped_nonpositive _ _ (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B)
    (radius₁_pos hδ.1 hB) hb he (radius₁_convex_left hδ hB hx).le u v

lemma rightRadius_convex_left {δ B t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) (ht : t ≤ 0) :
    0 < deriv (deriv (rightRadius δ B)) t := by
  change 0 < deriv (deriv (fun s => B/6*Collar.ell δ s)) t
  rw [deriv_const_mul_field',deriv_const_mul_field]
  exact mul_pos (div_pos hB (by norm_num)) (ell_convex_left hδ ht)
lemma neckModel_nonpositive_right {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {x : E3} (hx : 1 ≤ x 0) : NonpositiveAt (neckModel hδ hB) x := by
  apply (neckRightIsometry hδ hB).nonpositiveAt x (by change 2/3 < x 0; linarith)
  apply warpedModel_nonpositiveAt
  · exact rightRadius_pos δ hB _
  · apply (rightRadius_convex_left hδ hB _).le
    rw [neckFlip_apply]
    change 1-x 0 ≤ 0
    linarith
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
end ThreeManifold.Rechart
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature

lemma exponentialRadius_deriv : deriv exponentialRadius = fun t => -Real.exp (-t) := by
  funext t
  exact ((hasDerivAt_id t).neg.exp).deriv.trans (by simp)
lemma exponentialRadius_second (t : ℝ) : deriv (deriv exponentialRadius) t = Real.exp (-t) := by
  rw [exponentialRadius_deriv]
  exact (((hasDerivAt_id t).neg.exp).neg).deriv.trans (by simp)

lemma hyperbolicWarped_nonpositive (c : ℝ) (hc : c ≠ 0) (x : E3) :
    NonpositiveAt (hyperbolicWarped c hc) x := by
  apply warpedModel_nonpositiveAt
  · exact Real.exp_pos _
  · rw [exponentialRadius_second]
    exact (Real.exp_pos _).le

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece
lemma realUniversalMetric_nonpositive (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) :
    NonpositiveAt (realUniversalMetric c hc) x :=
  (universalLogIsometry c hc).nonpositiveAt x (mem_univ x) (hyperbolicWarped_nonpositive c hc _)
lemma realCoreMetric_nonpositive (c : ℝ) (hc : c ≠ 0) (q : WholePiece) :
    NonpositiveAt (realCoreMetric c hc) q := by
  let x : UniversalPiece := (HyperbolicCore.sectionMap q.1,CircleConstruction.sectionMap 6 q.2)
  have he : sourceProjection x = q := by
    apply Prod.ext
    · exact HyperbolicCore.sectionMap_rightInverse q.1
    · exact CircleConstruction.section_spec 6 q.2
  rw [← he]
  exact (coreProjectionIsometry c hc).nonpositiveAt_image (mem_univ x)
    (realUniversalMetric_nonpositive c hc x)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
lemma geodesic_congrOn (g : SmoothMetric M) {γ η : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (he : EqOn γ η U) (hγ : IsGeodesicOn g γ U) : IsGeodesicOn g η U := by
  refine ⟨hγ.1.congr he.symm,?_⟩
  intro c hc s hs hsc
  have hev : γ =ᶠ[nhds s] η := Filter.eventually_of_mem (hU.mem_nhds hs) (fun r hr => he hr)
  have hec : (c ∘ γ) =ᶠ[nhds s] (c ∘ η) := hev.fun_comp c
  have hcg := hγ.2 c hc s hs (by rwa [he hs])
  rw [along_congr g c hec.symm hec.deriv.symm]
  exact hcg
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
lemma deriv_injective {p : M} (hp : p ∈ P.domain) : Function.Injective (mfderiv I3 I3 f p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  by_contra hn
  have he := P.metric p hp v v
  have hpos := g.pos p v hn
  rw [hv,map_zero] at he
  change g.inner p v v = 0 at he
  linarith
lemma deriv_bijective {p : M} (hp : p ∈ P.domain) : Function.Bijective (mfderiv I3 I3 f p) := by
  change Function.Bijective (show E3 →L[ℝ] E3 from mfderiv I3 I3 f p)
  exact ⟨P.deriv_injective hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) rfl).mp
    (P.deriv_injective hp)⟩
lemma geodesic_reflect {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hg : IsGeodesicOn h (f ∘ γ) U) : IsGeodesicOn g γ U := by
  apply geodesic_of_acceleration_zero g hU hγ
  intro s hs
  apply P.deriv_injective (hγP hs)
  rw [map_zero]
  have he : velocity (f ∘ γ) =ᶠ[𝓝 s] P.mapField γ (velocity γ) := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact P.velocity_map (hγ.contMDiffAt (hU.mem_nhds hr)) (hγP hr)
  rw [← P.covariantDerivative_map hU hγ hγP (velocity_smooth hU hγ) hs,
    ← covariantDerivative_germ h he,geodesic_acceleration_zero h hU hg hs]
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise UpperHalfPlane
namespace ThreeManifold.WarpedCurvature
open RiemannianCoordinates Neck
end ThreeManifold.WarpedCurvature
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_1
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece
end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
variable {M N X : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {k : SmoothMetric X}
  {f : M → N} {w : N → X}
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder
lemma realNeck_nonpositive {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {q : Cylinder} (hq : q.1 ≤ 0 ∨ 1 ≤ q.1) : NonpositiveAt (realNeck hδ hB) q := by
  let x := coordinates (CylinderConstruction.sectionMap q)
  have he : euclideanProjection x = q := CylinderConstruction.section_spec q
  rw [← he]
  apply (neckProjectionIsometry hδ hB).nonpositiveAt_image (mem_univ x)
  rcases hq with hq|hq
  · exact neckModel_nonpositive_left hδ hB hq
  · exact neckModel_nonpositive_right hδ hB hq

lemma radial_nonpos {L r : ℝ} (hL : 4 ≤ L) (hr : r ≤ Real.log 2) :
    RadialProfile.coordinate L r ≤ 0 := by
  have he : RadialProfile.coordinate L (Real.log 2) = 0 := by
    rw [RadialProfile.coordinate_right (RadialProfile.log_bounds.1.le),sub_self,zero_div]
  rw [← he]
  exact (RadialProfile.coordinate_strictMono hL).monotone hr
lemma realLeftCylinder_nonpositive {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {q : Cylinder} (hq : q.1 ≤ Real.log 2) :
    NonpositiveAt (Rechart.realMetric coordinates (leftCylinder hδ)) q := by
  apply (radialIsometry (neck hδ (period_pos δ)) (leftLength_ge hδ)).nonpositiveAt q (mem_univ q)
  exact realNeck_nonpositive hδ (period_pos δ) (Or.inl (radial_nonpos (leftLength_ge hδ) hq))
lemma realRightCylinder_nonpositive {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {q : Cylinder} (hq : q.1 ≤ Real.log 2) :
    NonpositiveAt (Rechart.realMetric coordinates (rightCylinder hδ)) q := by
  apply (radialIsometry (switched (neck hδ (period_pos δ))) (L := 4) le_rfl).nonpositiveAt q (mem_univ q)
  apply (switchIsometry (neck hδ (period_pos δ))).nonpositiveAt _ (mem_univ _)
  apply realNeck_nonpositive hδ (period_pos δ)
  right
  change 1 ≤ 1-RadialProfile.coordinate 4 q.1
  linarith [radial_nonpos (L := 4) le_rfl hq]
end

open MetricConstruction CylinderConstruction RiemannianCoordinates

lemma cuspChart_apply {a : ℝ} (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    cuspChart a ha x = wholeCoordinates a ha ⟨x,hx⟩ := by
  unfold cuspChart
  change wholeCoordinates a ha ((wholeCusp a).openPartialHomeomorphSubtypeCoe
    (wholeCusp_nonempty a ha) |>.symm x) = _
  congr 1
  apply Subtype.ext
  exact (wholeCusp a).openPartialHomeomorphSubtypeCoe (wholeCusp_nonempty a ha) |>.right_inv (by simpa using hx)
lemma wholeCuspLog_height {a : ℝ} (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    (wholeCuspLog a ha x).1 = HyperbolicCore.height x.1 := by
  change Real.log ((cuspChart a ha x).1 : ℝ) = _
  rw [cuspChart_apply ha hx]
  exact (HyperbolicCore.height_cuspCoordinates a ha ⟨x.1,hx⟩).symm

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_1
variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
lemma whole_nonpositive {x : WholePiece} (hx : HyperbolicCore.height x.1 ≤ Real.log 2)
    (hn : ∀ q : Cylinder, q.1 ≤ Real.log 2 → NonpositiveAt (Rechart.realMetric coordinates g) q) :
    NonpositiveAt (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low)) x := by
  by_cases hh : x ∈ coreRegion
  · exact (wholeCoreIsometry g c hc low).nonpositiveAt x hh (realCoreMetric_nonpositive c hc x)
  · have hh' : x ∈ wholeCusp cuspLevel := by
      apply (HyperbolicCore.mem_cusp_iff_height cuspLevel_gt x.1).mpr
      rw [log_cuspLevel]
      change ¬HyperbolicCore.height x.1 < 1/4 at hh
      linarith
    apply (wholeCuspIsometry g c hc low).nonpositiveAt x hh'
    apply hn
    rwa [wholeCuspLog_height cuspLevel_gt hh']
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece_1
lemma realPiece_nonpositive {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool)
    {x : Piece} (hx : x ∉ collar) : NonpositiveAt (realPieceMetric hδ i) x := by
  have hh : HyperbolicCore.height x.1.1 ≤ Real.log 2 := by
    apply le_of_not_gt
    intro h
    exact hx ((HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ) < 2) x.1.1).mpr h)
  cases i
  · apply (pieceMapIsometry (leftWhole hδ)).nonpositiveAt x (mem_univ _)
    exact whole_nonpositive _ _ _ (leftCylinder_low hδ) hh (fun q hq => realLeftCylinder_nonpositive hδ hq)
  · apply (pieceMapIsometry (rightWhole hδ)).nonpositiveAt x (mem_univ _)
    exact whole_nonpositive _ _ _ (rightCylinder_low hδ) hh (fun q hq => realRightCylinder_nonpositive hδ hq)

lemma openNeck_isOpen : IsOpen openNeck :=
  (TwoGluing.inclusion_openEmbedding collar gluingMap false).isOpenMap _ collar.isOpen
lemma inclusion_collar_mem_openNeck (i : Bool) {x : Piece} (hx : x ∈ collar) :
    inclusion i x ∈ openNeck := by
  cases i
  · exact ⟨x,hx,rfl⟩
  · exact ⟨(gluingMap.symm ⟨x,hx⟩).1,(gluingMap.symm ⟨x,hx⟩).2,
      (TwoGluing.inclusion_symm_transition collar gluingMap ⟨x,hx⟩).symm⟩

lemma realCompactMetric_nonpositive_off_neck {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (p : GluedConstruction.Manifold) (hp : p ∉ openNeck) :
    NonpositiveAt (realCompactMetric hδ) p := by
  obtain ⟨i,x,rfl⟩ := TwoGluing.inclusion_surjective collar gluingMap p
  apply (pieceInclusionIsometry hδ i).nonpositiveAt_image (mem_univ x)
  apply realPiece_nonpositive hδ i
  exact fun hx => hp (inclusion_collar_mem_openNeck i hx)
end ThreeManifold.CompactMetric

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Passages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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
lemma interfaceBand_compact : IsCompact interfaceBand := by
  have hc : IsClosed {x : Piece | Real.log 2 ≤ HyperbolicCore.height x.1.1} :=
    isClosed_le continuous_const ((HyperbolicCore.height_continuous.comp continuous_subtype_val).comp continuous_fst)
  convert halfCore_compact.inter_right hc using 1
  ext x
  simp [interfaceBand,halfCore,and_comm]
lemma interfaceBand_subset_extended : interfaceBand ⊆ extendedPiece :=
  fun _ hx => RadialProfile.log_bounds.1.trans_le hx.1
lemma openNeck_subset_bands : openNeck ⊆
    inclusion false '' interfaceBand ∪ inclusion true '' interfaceBand := by
  rintro p ⟨x,hx,rfl⟩
  rcases halfCore_covers x with hl | ⟨ho,hr⟩
  · exact Or.inl ⟨x,⟨((HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ)<2) x.1.1).mp hx).le,hl⟩,rfl⟩
  · exact Or.inr ⟨(gluingMap ⟨x,ho⟩).1,⟨((HyperbolicCore.mem_cusp_iff_height
      (by norm_num : (1:ℝ)<2) _).mp (gluingMap ⟨x,ho⟩).2).le,hr⟩,
      (TwoGluing.inclusion_transition collar gluingMap ⟨x,ho⟩).symm⟩
lemma closure_openNeck_subset_extended : closure openNeck ⊆ extendedNeck := by
  have hc : IsClosed (inclusion false '' interfaceBand ∪ inclusion true '' interfaceBand) :=
    ((interfaceBand_compact.image (TwoGluing.inclusion_openEmbedding collar gluingMap false).continuous).isClosed).union
      ((interfaceBand_compact.image (TwoGluing.inclusion_openEmbedding collar gluingMap true).continuous).isClosed)
  exact (closure_minimal openNeck_subset_bands hc).trans (by
    rintro p (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)
    · exact Or.inl ⟨x,interfaceBand_subset_extended hx,rfl⟩
    · exact Or.inr ⟨x,interfaceBand_subset_extended hx,rfl⟩)

end ThreeManifold.CompactMetric

namespace ThreeManifold.CylinderConstruction

section
open QuotientConstruction

lemma lift_smoothAt {f : ℝ → Cylinder} {F : ℝ → P} {s : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,P) ∞ f s) (hF : ContinuousAt F s)
    (he : (projection ∘ F) =ᶠ[nhds s] f) : ContDiffAt ℝ ∞ F s := by
  let l := projection_cover.isCoveringMap.isLocalHomeomorph
  let e := l.localInverseAt (F s)
  have hes : f s ∈ e.source := by
    rw [← he.eq_of_nhds]
    exact l.apply_self_mem_localInverseAt_source
  have hsm := (local_inverse_smooth (F s) hes).comp s hf
  apply contMDiffAt_iff_contDiffAt.mp
  apply hsm.congr_of_eventuallyEq
  apply lifts_eventuallyEq l hF hsm.continuousAt
  · change F s = e (f s)
    rw [← he.eq_of_nhds]
    exact l.localInverseAt_apply_self.symm
  · have hne : ∀ᶠ t in nhds s, f t ∈ e.source :=
      hf.continuousAt (e.open_source.mem_nhds hes)
    filter_upwards [he,hne] with t ht ht'
    exact ht.trans (l.apply_localInverseAt_of_mem ht').symm

theorem exists_smooth_lift {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hUn : U.Nonempty) {f : ℝ → Cylinder}
    (hf : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,P) ∞ f U) :
    ∃ F : ℝ → P, ContDiffOn ℝ ∞ F U ∧ ∀ s ∈ U, projection (F s) = f s := by
  classical
  let : ContractibleSpace U := (convex_iff_ordConnected.mpr hUc).contractibleSpace hUn
  let : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  obtain ⟨s,hs⟩ := hUn
  let fU : C(U,Cylinder) := ⟨fun x => f x,continuousOn_iff_continuous_domRestrict.mp hf.continuousOn⟩
  obtain ⟨G,hG,-⟩ := projection_cover.isCoveringMap.existsUnique_continuousMap_lifts
    fU ⟨s,hs⟩ (sectionMap (f s)) (section_spec (f s))
  let F : ℝ → P := fun t => if ht : t ∈ U then G ⟨t,ht⟩ else 0
  have hF : ContinuousOn F U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert G.continuous using 1
    funext t
    exact dite_eq_left t.2
  have hFe : ∀ t ∈ U, projection (F t) = f t := by
    intro t ht
    dsimp only [F]
    rw [dite_eq_left ht]
    exact congr_fun hG.2 ⟨t,ht⟩
  refine ⟨F,fun t ht => ?_,hFe⟩
  apply (lift_smoothAt (hf.contMDiffAt (hU.mem_nhds ht))
    (hF.continuousAt (hU.mem_nhds ht)) ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds ht] with x hx
  exact hFe x hx

end

attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder_1
lemma exists_euclidean_smooth_lift {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hUn : U.Nonempty) {f : ℝ → Cylinder}
    (hf : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ f U) :
    ∃ F : ℝ → E3, ContDiffOn ℝ ∞ F U ∧ ∀ s ∈ U, euclideanProjection (F s) = f s := by
  have hfn : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,P) ∞ f U := by
    intro s hs
    exact (((Rechart.identity_smooth_backward coordinates) (f s)).comp s
      (hf.contMDiffAt (hU.mem_nhds hs))).contMDiffWithinAt
  obtain ⟨F,hF,he⟩ := exists_smooth_lift hU hUc hUn hfn
  refine ⟨coordinates ∘ F,coordinates.contDiff.comp_contDiffOn hF,?_⟩
  intro s hs
  simpa only [euclideanProjection,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using he s hs
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
lemma deriv_invertible {p : M} (hp : p ∈ P.domain) : (mfderiv I3 I3 f p).IsInvertible := by
  change (show E3 →L[ℝ] E3 from mfderiv I3 I3 f p).IsInvertible
  refine ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr (P.deriv_injective hp))
    (LinearMap.range_eq_top.mpr (P.deriv_bijective hp).2),?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

lemma map_unmap {γ : ℝ → M} (J : ∀ s, TangentSpace I3 ((f ∘ γ) s))
    {s : ℝ} (hs : γ s ∈ P.domain) : P.mapField γ (P.unmapField γ J) s = J s :=
  (P.deriv_invertible hs).self_apply_inverse _
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
omit [IsManifold I3 ∞ M] in
lemma fieldCoordinates_germ {γ η : ℝ → M} {J K : ℝ → E3} {s : ℝ}
    (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) (c : OpenPartialHomeomorph M E3) :
    fieldCoordinates γ J c =ᶠ[nhds s] fieldCoordinates η K c := by
  let A : M → E3 →L[ℝ] E3 := fun p => mfderiv I3 I3 c p
  change (fun r => A (γ r) (J r)) =ᶠ[nhds s] (fun r => A (η r) (K r))
  filter_upwards [hc,hJ] with r hr hr'
  rw [hr,hr']
lemma covariantDerivative_curve_germ (g : SmoothMetric M) {γ η : ℝ → M}
    {J K : ℝ → E3} {s : ℝ} (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) :
    covariantDerivative g γ J s = covariantDerivative g η K s := by
  let C : M → OpenPartialHomeomorph M E3 := chartAt E3
  let A : M → E3 →L[ℝ] E3 := fun p => mfderiv I3 I3 (C p).symm ((C p) p)
  change A (γ s) (alongDerivative g (C (γ s)) ((C (γ s)) ∘ γ) (fieldCoordinates γ J (C (γ s))) s) =
    A (η s) (alongDerivative g (C (η s)) ((C (η s)) ∘ η) (fieldCoordinates η K (C (η s))) s)
  rw [hc.eq_of_nhds]
  exact congrArg (A (η s)) (along_congr g _ (hc.fun_comp _) (fieldCoordinates_germ hc hJ _))
lemma curvatureAlong_curve_germ (g : SmoothMetric M) {γ η : ℝ → M}
    {J K : ℝ → E3} {s : ℝ} (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) :
    curvatureAlong g γ J s = curvatureAlong g η K s := by
  let C : M → OpenPartialHomeomorph M E3 := chartAt E3
  let A : M → E3 →L[ℝ] E3 := fun p => mfderiv I3 I3 (C p).symm ((C p) p)
  change A (γ s) (curvatureTerm g (C (γ s)) ((C (γ s)) (γ s))
    (fieldCoordinates γ J (C (γ s)) s) (deriv ((C (γ s)) ∘ γ) s) (deriv ((C (γ s)) ∘ γ) s)) =
    A (η s) (curvatureTerm g (C (η s)) ((C (η s)) (η s))
    (fieldCoordinates η K (C (η s)) s) (deriv ((C (η s)) ∘ η) s) (deriv ((C (η s)) ∘ η) s))
  rw [hc.eq_of_nhds,(fieldCoordinates_germ hc hJ _).eq_of_nhds,(hc.fun_comp (C (η s))).deriv_eq]
lemma indexPairDensity_curve_germ (g : SmoothMetric M) {γ η : ℝ → M}
    {J K : ℝ → E3} {s : ℝ} (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) :
    indexPairDensity g γ J J s = indexPairDensity g η K K s := by
  let B : M → E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner
  change B (γ s) (covariantDerivative g γ J s) (covariantDerivative g γ J s) -
    B (γ s) (curvatureAlong g γ J s) (J s) =
    B (η s) (covariantDerivative g η K s) (covariantDerivative g η K s) -
    B (η s) (curvatureAlong g η K s) (K s)
  rw [hc.eq_of_nhds,hJ.eq_of_nhds,covariantDerivative_curve_germ g hc hJ,
    curvatureAlong_curve_germ g hc hJ]
lemma smoothField_curve_congrOn {γ η : ℝ → M} {J K : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hc : EqOn γ η U) (hJK : EqOn J K U) (hJ : SmoothFieldOn γ J U) : SmoothFieldOn η K U := by
  intro c hca s hs
  have hsγ : γ s ∈ c.source := by rw [hc hs.1]; exact hs.2
  have hcg : γ =ᶠ[nhds s] η := Filter.eventually_of_mem (hU.mem_nhds hs.1) (fun r hr => hc hr)
  have hfg : J =ᶠ[nhds s] K := Filter.eventually_of_mem (hU.mem_nhds hs.1) (fun r hr => hJK hr)
  exact ((smoothField_coordinatesAt hU hγ hJ hca hs.1 hsγ).congr_of_eventuallyEq
    (fieldCoordinates_germ hcg hfg c).symm).contDiffWithinAt
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_3
theorem actual_neck_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) (hUc : OrdConnected U) (hUn : U.Nonempty)
    {γ : ℝ → GluedConstruction.Manifold} (hγ : IsGeodesicOn (realCompactMetric hδ) γ U)
    (hγe : MapsTo γ U extendedNeck) {J : ℝ → E3} (hJ : SmoothFieldOn γ J U) :
    ∃ (η V : ℝ → E3), IsGeodesicOn (normalizedNeck hδ) η U ∧ SmoothFieldOn η V U ∧
      (∀ s ∈ U, η s 0 = (neckPosition δ (γ s)).1) ∧
      (∀ s ∈ U, indexPairDensity (normalizedNeck hδ) η V V s =
        indexPairDensity (realCompactMetric hδ) γ J J s) ∧
      (∀ s ∈ U, J s = 0 → V s = 0) := by
  let P := neckPositionIsometry hδ
  let R := neckProjectionIsometry hδ (period_pos δ)
  let T := normalizationIsometry hδ (period_pos δ)
  let β := neckPosition δ ∘ γ
  have hβ := P.geodesic_map hU hγ hγe
  obtain ⟨F,hF,he⟩ := exists_euclidean_smooth_lift hU hUc hUn hβ.1
  have hFm : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ F U := contMDiffOn_iff_contDiffOn.mpr hF
  have hFR : MapsTo F U R.domain := fun _ _ => mem_univ _
  have hFg : IsGeodesicOn (neckModel hδ (period_pos δ)) F U :=
    R.geodesic_reflect hU hFm hFR (geodesic_congrOn _ hU (fun s hs => (he s hs).symm) hβ)
  let K := P.mapField γ J
  have hK : SmoothFieldOn β K U := P.mapField_smooth hU hγ.1 hγe hJ
  have hK' : SmoothFieldOn (euclideanProjection ∘ F) K U :=
    smoothField_curve_congrOn hU hβ.1 (fun s hs => (he s hs).symm) (fun _ _ => rfl) hK
  let W := R.unmapField F K
  have hW : SmoothFieldOn F W U := R.unmapField_smooth hU hFm hFR hK'
  have hFT : MapsTo F U T.domain := fun _ _ => mem_univ _
  refine ⟨normalize δ (period δ) ∘ F,T.mapField F W,T.geodesic_map hU hFg hFT,
    T.mapField_smooth hU hFm hFT hW,?_,?_,?_⟩
  · intro s hs
    exact congrArg Prod.fst (he s hs)
  · intro s hs
    rw [T.indexPairDensity_map hU hFm hFT hW hW hs,
      ← R.indexPairDensity_map hU hFm hFR hW hW hs]
    have hc : (euclideanProjection ∘ F) =ᶠ[nhds s] β :=
      Filter.eventually_of_mem (hU.mem_nhds hs) (fun r hr => he r hr)
    have hf : R.mapField F W =ᶠ[nhds s] K :=
      Filter.eventually_of_mem (hU.mem_nhds hs) (fun r hr => R.map_unmap K (hFR hr))
    rw [indexPairDensity_curve_germ _ hc hf]
    exact P.indexPairDensity_map hU hγ.1 hγe hJ hJ hs
  · intro s _ hs
    have hK0 : K s = 0 := by
      exact (congrArg (mfderiv I3 I3 (neckPosition δ) (γ s)) hs).trans
        ((mfderiv I3 I3 (neckPosition δ) (γ s)).map_zero)
    have hW0 : W s = 0 := by
      exact (congrArg (mfderiv I3 I3 euclideanProjection (F s)).inverse hK0).trans
        ((mfderiv I3 I3 euclideanProjection (F s)).inverse.map_zero)
    exact (congrArg (mfderiv I3 I3 (normalize δ (period δ)) (F s)) hW0).trans
      ((mfderiv I3 I3 (normalize δ (period δ)) (F s)).map_zero)
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
theorem actual_finite_neck_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck)
    {J : ℝ → E3} (hJ : SmoothFieldOn γ J U) :
    ∃ (W : Set ℝ) (η V : ℝ → E3), IsOpen W ∧ OrdConnected W ∧
      Icc a b ⊆ W ∧ W ⊆ U ∧ IsGeodesicOn (normalizedNeck hδ) η W ∧ SmoothFieldOn η V W ∧
      (∀ s ∈ W, η s 0 = (neckPosition δ (γ s)).1) ∧
      (∀ s ∈ W, indexPairDensity (normalizedNeck hδ) η V V s =
        indexPairDensity (realCompactMetric hδ) γ J J s) ∧ (∀ s ∈ W, J s = 0 → V s = 0) := by
  obtain ⟨W,hW,hWc,hcc,hWU,hWe⟩ := finite_neck_neighborhood hδ hU hγ hab hsub hr
  have hγW : IsGeodesicOn (realCompactMetric hδ) γ W := ⟨hγ.1.mono hWU,fun c hc s hs hsc => hγ.2 c hc s (hWU hs) hsc⟩
  obtain ⟨η,V,hη,hV,hh,hi,hz⟩ := actual_neck_lift hδ hW hWc
    ⟨a,hcc ⟨le_rfl,hab.le⟩⟩ hγW hWe (fun c hc => (hJ c hc).mono (inter_subset_inter_left _ hWU))
  exact ⟨W,η,V,hW,hWc,hcc,hWU,hη,hV,hh,hi,hz⟩
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
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem actual_finite_neck_index {δ C a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ : ℝ → GluedConstruction.Manifold} {J : ℝ → E3}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck)
    (ha : γ a ∉ openNeck ∨ J =ᶠ[𝓝 a] 0) (hb : γ b ∉ openNeck ∨ J =ᶠ[𝓝 b] 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (realCompactMetric hδ) γ J J s := by
  obtain ⟨W,η,V,hW,_,hcc,_,hη,hV,hh,hi,hz⟩ := actual_finite_neck_lift hδ hU hγ hab hsub hr hJ
  obtain ⟨ht,hleft,hright⟩ := finite_neck_height_boundary hδ hU hγ hab hsub hr
  have hzero (s : ℝ) (hs : s ∈ Icc a b) (hJs : J =ᶠ[𝓝 s] 0) : V =ᶠ[𝓝 s] 0 := by
    filter_upwards [hW.mem_nhds (hcc hs),hJs] with r hrw hrj
    exact hz r hrw hrj
  have he := finite_neck_index hδ hC hsmall hB hW hab hcc hη hV
    (fun s hs => by rw [hh s (hcc hs)]; exact ht s hs)
    (fun s hs => by
      rw [hh s (hcc (Ioo_subset_Icc_self hs))]
      exact (neckPosition_mem_iff δ (closure_openNeck_subset_extended (subset_closure (hr s hs)))).mpr (hr s hs))
    (by rcases ha with ha | ha
        · exact Or.inl (by rw [hh a (hcc (left_mem_Icc.mpr hab.le))]; exact hleft ha)
        · exact Or.inr (hzero a (left_mem_Icc.mpr hab.le) ha))
    (by rcases hb with hb | hb
        · exact Or.inl (by rw [hh b (hcc (right_mem_Icc.mpr hab.le))]; exact hright hb)
        · exact Or.inr (hzero b (right_mem_Icc.mpr hab.le) hb))
  convert he using 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact (hi s (hcc (by simpa only [uIcc_of_le hab.le] using hs))).symm
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma compact_interval_window {K U : Set ℝ} (hK : IsCompact K) (hKn : K.Nonempty)
    (hU : IsOpen U) (hUc : OrdConnected U) (hKU : K ⊆ U) :
    ∃ A B : ℝ, A < B ∧ K ⊆ Ioo A B ∧ Icc A B ⊆ U := by
  obtain ⟨a,ha⟩ := hK.exists_isLeast hKn
  obtain ⟨b,hb⟩ := hK.exists_isGreatest hKn
  obtain ⟨A,B,hAa,hbB,hAB⟩ := IndexForm.interval_enlargement hU hUc (hKU ha.1) (hKU hb.1)
  exact ⟨A,B,hAa.trans_le ((ha.2 hb.1).trans hbB.le),fun s hs => ⟨hAa.trans_le (ha.2 hs),(hb.2 hs).trans_lt hbB⟩,hAB⟩

theorem realCompactMetric_nonnegative_index {δ C : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {γ : ℝ → GluedConstruction.Manifold} (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) :
    NonnegativeIndexOn (realCompactMetric hδ) γ U := by
  intro J hJ hJc hJU
  by_cases hJn : (tsupport J).Nonempty
  swap
  · apply integral_nonneg
    intro s
    have hz : indexPairDensity (realCompactMetric hδ) γ J J s = 0 := by
      by_contra hn
      exact hJn ⟨s,indexPairDensity_support _ γ J J hn⟩
    exact hz.ge
  obtain ⟨A,B,hAB,hcut,hsub⟩ := compact_interval_window hJc hJn hU hUc hJU
  let P := Ioo A B ∩ γ ⁻¹' openNeck
  have hγAB : ContinuousOn γ (Ioo A B) := hγ.1.continuousOn.mono (Ioo_subset_Icc_self.trans hsub)
  have hP : IsOpen P := hγAB.isOpen_inter_preimage isOpen_Ioo openNeck_isOpen
  have hzero (s : ℝ) (hs : s ∉ Ioo A B) : J =ᶠ[𝓝 s] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun hx => hs (hcut hx))
  apply GlobalAssembly.integral_nonneg_of_passages hP
    (indexPairDensity_integrable _ hU hγ.1 hJ hJ hJc hJU)
  · intro x hx
    obtain ⟨a,b,hab,hAa,hbB,hcomp,ha,hb⟩ := FinitePassage.bounded_component hP inter_subset_left hx
    have hrange : ∀ s ∈ Ioo a b, γ s ∈ openNeck := by
      intro s hs
      exact (connectedComponentIn_subset P x (hcomp.symm.subset hs)).2
    have he := FinitePassage.endpoint_alternative hab hAa hbB hrange (hγ.1.continuousOn.mono hsub) ha hb
    have hi := actual_finite_neck_index hδ hC hsmall hB hU hab
      ((Icc_subset_Icc hAa hbB).trans hsub) hγ hJ hrange
      (by rcases he.1 with he | he
          · exact Or.inr (hzero a (by rw [he]; simp))
          · exact Or.inl he.2)
      (by rcases he.2 with he | he
          · exact Or.inr (hzero b (by rw [he]; simp))
          · exact Or.inl he.2)
    rw [hcomp]
    simpa only [intervalIntegral.integral_of_le hab.le,integral_Ioc_eq_integral_Ioo] using hi
  · intro s hs
    by_cases hin : s ∈ Ioo A B
    · exact indexPairDensity_nonneg_of_nonpositiveAt _ J
        (hγ.1.contMDiffAt (hU.mem_nhds (hsub (Ioo_subset_Icc_self hin))))
        (realCompactMetric_nonpositive_off_neck hδ (γ s) (fun hh => hs ⟨hin,hh⟩))
    · have hd : indexPairDensity (realCompactMetric hδ) γ J J s = 0 := by
        by_contra hn
        exact hin (hcut (indexPairDensity_support _ γ J J hn))
      exact hd.ge

end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.CompactMetric
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.realCompactMetric_nonnegative_index := @_root_.OAI.ThreeManifold.CompactMetric.realCompactMetric_nonnegative_index
