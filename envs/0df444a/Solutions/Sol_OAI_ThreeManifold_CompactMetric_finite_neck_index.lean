-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.finite_neck_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:22:03.158853+00:00
-- url     : https://prove2.me/submissions/96e8d615-7b51-49d2-b2a0-7e948667af28

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L1475-L1533
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.finite_neck_index. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_coordinate_index_integral
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_momentum_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_monotone_index
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_scalar_equation
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_truncated_return_index
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_normalizedRight_bilin
import Theorems.Thm_OAI_ThreeManifold_Neck_curvatureTerm_product
import Theorems.Thm_OAI_ThreeManifold_Neck_energy_cometric_identity
import Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_finite_turn_completion
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_reflected_closed_equations
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_reflection
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_curvature
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_coordinate_derivative
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_covariantDerivative_map
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_unmapField_smooth
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_euclidean_affine_geodesic
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_euclidean_affine_index_integral
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_geodesic_of_acceleration_zero

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

end ThreeManifold.RadialProfile
end

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric

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

lemma rate_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    HasDerivAt (rate δ)
      (δ * (deriv a t * denom δ t - δ * a t ^ 2) / (2 * denom δ t ^ 2)) t := by
  have hd : denom δ t ≠ 0 := ne_of_gt (denom_pos hδ ht)
  convert! (((a_hasDerivAt t).const_mul δ).div
    ((denom_hasDerivAt δ t).const_mul 2) (mul_ne_zero (by norm_num) hd)) using 1
  rw [← (a_hasDerivAt t).deriv]
  field_simp
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

lemma Q_formula_of_ne {δ t : ℝ} (h1 : d₁ δ t ≠ 0) (h2 : d₂ δ t ≠ 0) :
    Q δ t = !![1 / d₁ δ t, -shear δ t / d₁ δ t;
      -shear δ t / d₁ δ t, 1 / d₂ δ t + shear δ t ^ 2 / d₁ δ t] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp; ring

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

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

lemma positive_return_has_stationary_maximum {t v : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s) :
    ∃ c ∈ Ioo 0 L, 0 < t c ∧ v c = 0 ∧ IsMaxOn t (Icc 0 L) c := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hL.le) (HasDerivAt.continuousOn ht)
  have hp := hpos (L / 2) ⟨by linarith, by linarith⟩
  have hcm : 0 < t c := lt_of_lt_of_le hp (hmax ⟨by linarith, by linarith⟩)
  have hc' : c ∈ Ioo 0 L := by
    constructor
    · by_contra hn
      have he : c = 0 := by linarith [hc.1]
      rw [he, h0] at hcm
      exact lt_irrefl _ hcm
    · by_contra hn
      have he : c = L := by linarith [hc.2]
      rw [he, hL0] at hcm
      exact lt_irrefl _ hcm
  refine ⟨c, hc', hcm, ?_, hmax⟩
  exact (hmax.isLocalMax (Icc_mem_nhds hc'.1 hc'.2)).hasDerivAt_eq_zero (ht c hc)

lemma return_midpoint {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L c : ℝ} (hc : c ∈ Ioo 0 L)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s)
    (hvc : v c = 0) : c = L / 2 := by
  rcases lt_trichotomy c (L / 2) with h | h | h
  · have hsub : Icc (0 : ℝ) (2 * c) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
    have hh := scalar_reflection hF (show c ∈ Ioo (0 : ℝ) (2 * c) from
      ⟨hc.1, by linarith [hc.1]⟩) (by ring : 0 + 2 * c = 2 * c)
      (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs)) hvc
    have he := (hh 0 ⟨le_rfl, by linarith [hc.1]⟩).1
    simp only [sub_zero, h0] at he
    have hp := hpos (2 * c) ⟨by linarith [hc.1], by linarith⟩
    exact False.elim (by linarith)
  · exact h
  · have hsub : Icc (2 * c - L) L ⊆ Icc 0 L := Icc_subset_Icc (by linarith) le_rfl
    have hh := scalar_reflection hF (show c ∈ Ioo (2 * c - L) L from
      ⟨by linarith [hc.2], hc.2⟩) (by ring : 2 * c - L + L = 2 * c)
      (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs)) hvc
    have he := (hh L ⟨by linarith [hc.2], le_rfl⟩).1
    rw [hL0] at he
    have hp := hpos (2 * c - L) ⟨by linarith, by linarith [hc.2]⟩
    exact False.elim (by linarith)

lemma actual_return_symmetry {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s) :
    v (L / 2) = 0 ∧ IsMaxOn t (Icc 0 L) (L / 2) ∧
      ∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s := by
  obtain ⟨c, hc, _, hvc, hm⟩ := positive_return_has_stationary_maximum hL ht h0 hL0 hpos
  have he := return_midpoint hF hc ht hv h0 hL0 hpos hvc
  subst c
  refine ⟨hvc, hm, ?_⟩
  have hh := scalar_reflection hF (show L / 2 ∈ Ioo (0 : ℝ) L from
    ⟨by linarith, by linarith⟩) (by ring : 0 + L = 2 * (L / 2)) ht hv hvc
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

lemma contDiff_pairing_const {R : ℝ → TMat} {n : WithTop ℕ∞}
    (hR : ContDiff ℝ n R) (p q : TVec) : ContDiff ℝ n (fun u => pairing (R u) p q) := by
  simp only [pairing, Matrix.mulVec, dotProduct]
  fun_prop

lemma force_smooth (right : Bool) (δ : ℝ) (p : TVec) :
    ContDiff ℝ ∞ (force right δ p) :=
  contDiff_pairing_const (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2 p p

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

lemma matrix_inverse_second_deriv {R : ℝ → TMat} {s : ℝ}
    (hR : ContDiff ℝ ∞ R) (hdet : (R s).det ≠ 0) :
    deriv (deriv (fun u => (R u)⁻¹)) s =
      (2 : ℝ) • ((R s)⁻¹ * deriv R s * (R s)⁻¹ * deriv R s * (R s)⁻¹) -
        (R s)⁻¹ * deriv (deriv R) s * (R s)⁻¹ := by
  have hQ := ((matrix_inverse_smoothAt hR.contDiffAt hdet).differentiableAt (by simp)).hasDerivAt
  have hRd : HasDerivAt (deriv R) (deriv (deriv R) s) s := ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp)).differentiableAt.hasDerivAt
  have h := matrix_mul_hasDerivAt (matrix_mul_hasDerivAt hQ.neg hRd) hQ
  have he : deriv (fun u => (R u)⁻¹) =ᶠ[nhds s]
      (fun u => -(R u)⁻¹ * deriv R u * (R u)⁻¹) := by
    filter_upwards [(contDiffAt_det_two hR.contDiffAt).continuousAt.eventually_ne hdet] with u hu
    exact matrix_inverse_first_deriv hR hu
  have hh : deriv (deriv (fun u => (R u)⁻¹)) s =
      ((-deriv (fun u => (R u)⁻¹) s * deriv R s + (- (R s)⁻¹) * deriv (deriv R) s) * (R s)⁻¹ +
        (-(R s)⁻¹) * deriv R s * deriv (fun u => (R u)⁻¹) s) :=
    (h.congr_of_eventuallyEq he).deriv
  rw [hh, matrix_inverse_first_deriv hR hdet]
  simp only [neg_mul, mul_neg, neg_neg, add_mul, ← Matrix.mul_assoc]
  module

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma derivative_transpose {R : ℝ → TMat} (hs : ∀ u, (R u)ᵀ = R u)
    {s : ℝ} (hR : DifferentiableAt ℝ R s) : (deriv R s)ᵀ = deriv R s := by
  ext i j
  have hij : (fun u => R u j i) = (fun u => R u i j) := by
    funext u
    exact congrArg (fun m : TMat => m i j) (hs u)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f s) hij
  rw [(hasDerivAt_pi.mp (hasDerivAt_pi.mp hR.hasDerivAt j) i).deriv,
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hR.hasDerivAt i) j).deriv] at hd
  exact hd

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma metricInverse_transpose (right : Bool) (δ u : ℝ) :
    (metricInverse right δ u)ᵀ = metricInverse right δ u := by
  simp only [metricInverse, Matrix.transpose_nonsing_inv,
    coordinateCometric_transpose]

lemma symmetric_total_deriv {Q : ℝ → TMat} (hs : ∀ u, (Q u)ᵀ = Q u) (u : ℝ) :
    (deriv Q u)ᵀ = deriv Q u := by
  by_cases hQ : DifferentiableAt ℝ Q u
  · exact derivative_transpose hs hQ
  · have hd : deriv Q u = 0 := deriv_zero_of_not_differentiableAt hQ
    rw [hd]
    rfl

lemma metricInverse_first {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    deriv (metricInverse right δ) u =
      -metricInverse right δ u * deriv (coordinateCometric right δ) u * metricInverse right δ u :=
  matrix_inverse_first_deriv (coordinateCometric_smooth right δ) hdet

lemma metricInverse_second {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    deriv (deriv (metricInverse right δ)) u =
      (2 : ℝ) • (metricInverse right δ u * deriv (coordinateCometric right δ) u *
        metricInverse right δ u * deriv (coordinateCometric right δ) u * metricInverse right δ u) -
      metricInverse right δ u * deriv (deriv (coordinateCometric right δ)) u * metricInverse right δ u :=
  matrix_inverse_second_deriv (coordinateCometric_smooth right δ) hdet

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
end ThreeManifold.WarpedCurvature

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature
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

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
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
end

open MetricConstruction CylinderConstruction RiemannianCoordinates

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_1
variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
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
end ThreeManifold.CompactMetric

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

lemma ell_sq_eq_inv {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : -1/4 < t) :
    (Collar.ell δ t)^2 = 1 / d₁ δ t := by
  have hd : d₁ δ t ≠ 0 := (Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)).ne'
  exact (eq_div_iff hd).mpr (Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ ht)
lemma normalizedNeck_bilin {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) (u v : E3) :
    (normalizedNeck hδ).inner x u v = Neck.metric (Q δ (x 0)) (splitVector u) (splitVector v) := by
  have ht2 : -1/4 < 1-x 0 := by linarith [hx.2]
  have h1 : d₁ δ (x 0) ≠ 0 := (Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith [hx.1] : -1 ≤ x 0)).ne'
  have h2 : d₂ δ (x 0) ≠ 0 := (Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith [hx.2] : -1 ≤ 1-x 0)).ne'
  rw [normalizedNeck_apply,ell_sq_eq_inv hδ hx.1,ell_sq_eq_inv hδ ht2,
    LocalNeck.Q_formula_of_ne h1 h2]
  simp only [Neck.metric,splitVector,Neck.pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,d₂,d₁,shear]
  ring
lemma normalizedNeck_matrix {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) :
    metricMatrix (normalizedNeck hδ) (OpenPartialHomeomorph.refl E3) x = blockMatrix (Q δ (x 0)) := by
  ext i j
  change (normalizedNeck hδ).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change (normalizedNeck hδ).inner x (basisVector i) (basisVector j) = _
  rw [normalizedNeck_bilin hδ hx]
  fin_cases i <;> fin_cases j <;>
    simp [Neck.metric,splitVector,Neck.pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,basisVector,blockMatrix]
lemma normalizedNeck_matrix_germ {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) :
    metricMatrix (normalizedNeck hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[nhds x]
      fun y => blockMatrix (Q δ (y 0)) := by
  have hx' : x 0 ∈ Ioo (-1/4:ℝ) (5/4) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  filter_upwards [(continuous_apply 0).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx')] with y hy
  exact normalizedNeck_matrix hδ hy
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
lemma euclidean_velocity {γ : ℝ → E3} : velocity γ = deriv γ := by
  funext s
  unfold velocity
  rw [mfderiv_eq_fderiv]
  rfl

end

section
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

lemma normalizedRight_matrix {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) :
    metricMatrix (normalizedRight hδ) (OpenPartialHomeomorph.refl E3) x =
      blockMatrix (metricInverse true δ (x 0)) := by
  ext i j
  change (normalizedRight hδ).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change (normalizedRight hδ).inner x (basisVector i) (basisVector j) = _
  rw [normalizedRight_bilin hδ hx]
  fin_cases i <;> fin_cases j <;>
    simp [metric,splitVector,pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,basisVector,blockMatrix]
lemma normalizedRight_matrix_germ {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) :
    metricMatrix (normalizedRight hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[nhds x]
      fun y => blockMatrix (metricInverse true δ (y 0)) := by
  have hx' : x 0 ∈ Ioo (-1/4:ℝ) (5/4) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  filter_upwards [(continuous_apply 0).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx')] with y hy
  exact normalizedRight_matrix hδ hy

lemma framedNeck_matrix_germ (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) :
    metricMatrix (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[nhds x]
      fun y => blockMatrix (metricInverse right δ (y 0)) := by
  cases right
  · exact normalizedNeck_matrix_germ hδ hx
  · exact normalizedRight_matrix_germ hδ hx

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

lemma frame_QP (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    metricInverse right δ t * coordinateCometric right δ t = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (frame_det_ne right hδ ht))
lemma frame_PQ (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    coordinateCometric right δ t * metricInverse right δ t = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (frame_det_ne right hδ ht))
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma framed_velocity_torus (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (splitVector (deriv γ s)).2 = coordinateCometric right δ (γ s 0) *ᵥ p := by
  rw [← hp,mulVec_mulVec,frame_PQ right ⟨hδ.1.le,hδ.2⟩ ht,one_mulVec]

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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
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

lemma coordinateCometric_end_third (right : Bool) {δ t : ℝ} (ht : t < 1/3) :
    coordinateCometric right δ t = !![1+δ*A t,0;0,1+δ*A 1] := by
  cases right
  · have hc := χ_eq_zero (show t ≤ 5/12 by linarith)
    have hA := A_plateau (show 2/3 ≤ 1-t by linarith) (show (2/3:ℝ) ≤ 1 by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateCometric,P,d₁,d₂,shear,hc,hA]
  · have hc := χ_eq_one (show 7/12 ≤ 1-t by linarith)
    have hA := A_plateau (show 2/3 ≤ 1-t by linarith) (show (2/3:ℝ) ≤ 1 by norm_num)
    have he : 1-(1-t) = t := by ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateCometric,PEnd,C₂,P,d₁,d₂,shear,hc,hA,he,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.transpose_apply] <;> ring

lemma metricInverse_end_warped (right : Bool) {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (ht : t ∈ Ioo (-1/4:ℝ) (1/3)) :
    metricInverse right δ t = WarpedCurvature.Q (Collar.ell δ) (Collar.ell δ 1) t := by
  unfold metricInverse
  rw [coordinateCometric_end_third right ht.2]
  apply Matrix.inv_eq_left_inv
  have h0 := Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ ht.1
  have h1 := Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ (by norm_num : (-1/4:ℝ) < 1)
  change (Collar.ell δ t)^2 * (1+δ*A t) = 1 at h0
  change (Collar.ell δ 1)^2 * (1+δ*A 1) = 1 at h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WarpedCurvature.Q,WarpedCurvature.diag,Matrix.mul_apply,Fin.sum_univ_two,h0,h1]

lemma ell_convex_nonnegative {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : 0 ≤ t) :
    0 ≤ deriv (deriv (Collar.ell δ)) t := by
  have he : Collar.k δ =ᶠ[𝓝 t] Collar.rate δ := by
    filter_upwards [Ioi_mem_nhds (show (-1/4:ℝ) < t by linarith)] with u hu
    exact Collar.k_eq_rate hu.le
  have hk : deriv (Collar.k δ) t ≤ 0 := by
    rw [he.deriv_eq,(Collar.rate_hasDerivAt ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonneg_of_nonpos hδ.1.le
      have hd := Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)
      have ha := mul_nonpos_of_nonpos_of_nonneg (a_deriv_nonpos t) hd.le
      have hq := mul_nonneg hδ.1.le (sq_nonneg (a t))
      linarith
    · positivity
  rw [Collar.ell_second ⟨hδ.1.le,hδ.2⟩]
  exact mul_nonneg (sub_nonneg.mpr (hk.trans (sq_nonneg _))) (Collar.ell_pos δ t).le

lemma framed_neck_shallow_nonpositive (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {x : E3} (hx : x 0 ∈ Icc (0:ℝ) (1/4)) : NonpositiveAt (framedNeck right hδ) x := by
  have he : metricMatrix (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[𝓝 x]
      fun y => blockMatrix (WarpedCurvature.Q (Collar.ell δ) (Collar.ell δ 1) (y 0)) := by
    filter_upwards [framedNeck_matrix_germ right hδ ⟨hx.1,by linarith [hx.2]⟩,
      ((continuous_apply 0).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (show x 0 ∈ Ioo (-1/4:ℝ) (1/3) from ⟨by linarith [hx.1],by linarith [hx.2]⟩)))] with y hy ht
    rw [hy,metricInverse_end_warped right hδ ht]
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  exact WarpedCurvature.warped_nonpositive _ _ (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)
    (Collar.ell_pos δ) (Collar.ell_pos δ 1).ne' he (ell_convex_nonnegative hδ hx.1) u v

lemma framed_shallow_index (right : Bool) {δ a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} (hab : a ≤ b)
    (hγ : ∀ s ∈ Icc a b, ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s)
    (ht : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) (1/4)) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  exact indexPairDensity_nonneg_of_nonpositiveAt _ J (hγ s hs) (framed_neck_shallow_nonpositive right hδ (ht s hs))
end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
lemma finite_turn_maximum {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {b c : ℝ} (hc : c ∈ Ioo 0 b)
    (ht : ∀ s ∈ Icc 0 b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (ha : t 0 = 0) (hr : ∀ s ∈ Ioo 0 b, t s ∈ Ioo (0:ℝ) 1) :
    ∀ s ∈ Icc 0 b, t s ≤ t c := by
  have hd := reflected_closed_equations hF hc ht hv hvc
  have hh := finite_turn_completion hF hc ht hv hvc ha hr
  simp only [sub_zero] at hd hh
  have hm := (actual_return_symmetry hF (by linarith [hc.1] : 0 < 2*c)
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2) hh.2.2.2.1 hh.2.2.2.2.1
    (fun s hs => (hh.2.2.2.2.2 s hs).1)).2.1
  rw [show 2*c/2 = c by ring] at hm
  intro s hs
  have he := hm ⟨hs.1,hs.2.trans hh.1⟩
  change reflectEven c t s ≤ reflectEven c t c at he
  rw [hh.2.1 hs,reflectEven,ite_eq_left le_rfl] at he
  exact he
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem framed_turn_index (right : Bool) {δ C L c : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hc : c ∈ Ioo 0 L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hvc : deriv γ c 0 = 0) (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (henergy : ∀ s ∈ Icc 0 L,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  by_cases hstar : 1/4 < γ c 0
  · exact framed_truncated_return_index right hδ hC hsmall hb hU hsub hc hγ hJ hp h0 hrc hend hvc hr hstar henergy
  · have ht (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt (fun r => γ r 0) (deriv γ s 0) s :=
      hasDerivAt_pi.mp (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))).differentiableAt (by simp)).hasDerivAt 0
    have hm := PassageDynamics.finite_turn_maximum (force_smooth right δ p) hc ht
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs)) hvc h0 hr
    apply framed_shallow_index right hδ (hc.1.trans hc.2).le
      (fun s hs => hγ.1.contMDiffAt (hU.mem_nhds (hsub hs)))
    intro s hs
    exact ⟨(hrc s hs).1,(hm s hs).trans (le_of_not_gt hstar)⟩
end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma framed_energy_nonneg (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) {p : TVec}
    (hc : 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) p)
    (v : ℝ) (V D : Vec) :
    0 ≤ coordinateEnergyDensity (metricInverse right δ t) (deriv (metricInverse right δ) t)
      (deriv (deriv (metricInverse right δ)) t) (v,coordinateCometric right δ t *ᵥ p) V D := by
  rw [metricInverse_first (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),
    metricInverse_second (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),
    energy_cometric_identity (frame_QP right ⟨hδ.1.le,hδ.2⟩ ht)
      (coordinateCometric_transpose right δ _) (metricInverse_transpose right δ _)
      (symmetric_total_deriv (coordinateCometric_transpose right δ) t)]
  have hp := (coordinateCometric_posDef (fun q => (frame_elliptic right ⟨hδ.1.le,hδ.2⟩ ht q).1)).inv.posSemidef
  have hh := hp.dotProduct_mulVec_nonneg (D.2-V.1 • (deriv (coordinateCometric right δ) t *ᵥ p))
  simp only [star_trivial] at hh
  change 0 ≤ pairing (metricInverse right δ t) _ _ at hh
  have hc' : pairing (deriv (deriv (coordinateCometric right δ)) t) p p ≤ 0 := by
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) t) p p at hc
    rw [pairing_matrix_neg] at hc
    linarith
  have hn := mul_nonpos_of_nonpos_of_nonneg hc' (sq_nonneg V.1)
  nlinarith [sq_nonneg D.1]
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
lemma framed_zero_endpoints_index (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hc : ∀ t ∈ Icc (0:ℝ) 1, ∀ p, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) p)
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1) (hJa : J a = 0) (hJb : J b = 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  rw [framed_coordinate_index_integral right hδ hU hγ hJ
    (by simpa only [uIcc_of_le hab] using hsub) (by simpa only [uIcc_of_le hab] using htr)]
  have hb0 (s : ℝ) (hJs : J s = 0) :
      boundaryTerm (deriv (metricInverse right δ) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s)) = 0 := by
    simp [hJs, splitVector, boundaryTerm, pairing]
  rw [hb0 b hJb,hb0 a hJa,sub_self,sub_zero]
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  let p := metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2
  have hu := framed_velocity_torus right hδ (htr s hs) (show metricInverse right δ (γ s 0) *ᵥ
    (splitVector (deriv γ s)).2 = p from rfl)
  have hT : splitVector (deriv γ s) = ((splitVector (deriv γ s)).1,coordinateCometric right δ (γ s 0) *ᵥ p) := by
    rw [← hu]
  rw [hT]
  exact framed_energy_nonneg right hδ (htr s hs) (hc _ (htr s hs) p) _ _ _

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

lemma euclidean_curvature (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    curvatureAlong g γ J s = curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s)
      (J s) (deriv γ s) (deriv γ s) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma euclidean_smoothField {γ J : ℝ → E3} {U : Set ℝ} (hJ : ContDiffOn ℝ ∞ J U) :
    SmoothFieldOn γ J U := by
  intro c hc
  have he := chartedSpaceSelf_atlas.mp hc
  subst c
  rw [euclidean_fieldCoordinates]
  exact hJ.mono inter_subset_left

lemma affine_hasDerivAt {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    HasDerivAt (fun r => f (a+k*r)) (k • deriv f (a+k*s)) s := by
  convert hf.hasDerivAt.scomp s (((hasDerivAt_id s).const_mul k).const_add a) using 1 <;> first | rfl | simp

lemma affine_deriv {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    deriv (fun r => f (a+k*r)) s = k • deriv f (a+k*s) := (affine_hasDerivAt hf).deriv

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

lemma fromRight_toRight (δ : ℝ) (x : E3) : fromRight δ (toRight δ x) = x := by
  change fromRightLinear δ ((fromRightLinear δ).symm (x - ![1,0,0])) + ![1,0,0] = x
  rw [ContinuousLinearEquiv.apply_symm_apply,sub_add_cancel]
lemma toRight_height (δ : ℝ) (x : E3) : toRight δ x 0 = 1-x 0 := by
  change -(x 0-1) = 1-x 0
  ring
lemma toRight_smooth (δ : ℝ) : ContDiff ℝ ∞ (toRight δ) :=
  (fromRightLinear δ).symm.contDiff.comp (contDiff_id.sub contDiff_const)

theorem right_frame_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ J : ℝ → E3}
    (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U) :
    ∃ η V : ℝ → E3, IsGeodesicOn (framedNeck true hδ) η U ∧ SmoothFieldOn η V U ∧
      (∀ s, η s 0 = 1-γ s 0) ∧
      (∀ s ∈ U, indexPairDensity (framedNeck true hδ) η V V s =
        indexPairDensity (normalizedNeck hδ) γ J J s) ∧
      (∀ s, J s = 0 → V s = 0) ∧
      (∀ s ∈ U, (framedNeck true hδ).inner (η s) (velocity η s) (velocity η s) =
        (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s)) := by
  let R := fromRightIsometry hδ
  let η := toRight δ ∘ γ
  have he : fromRight δ ∘ η = γ := by funext s; exact fromRight_toRight δ (γ s)
  have hη : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ η U :=
    contMDiffOn_iff_contDiffOn.mpr ((toRight_smooth δ).comp_contDiffOn (euclidean_curve_smooth hγ.1))
  have hηR : MapsTo η U R.domain := fun _ _ => mem_univ _
  have hg : IsGeodesicOn (normalizedRight hδ) η U :=
    R.geodesic_reflect hU hη hηR (by simpa only [he] using hγ)
  have hf : SmoothFieldOn (fromRight δ ∘ η) J U :=
    smoothField_curve_congrOn hU hγ.1 (fun s _ => (congrFun he s).symm) (fun _ _ => rfl) hJ
  let V := R.unmapField η J
  have hV := R.unmapField_smooth hU hη hηR hf
  refine ⟨η,V,hg,hV,fun s => toRight_height δ (γ s),?_,?_,?_⟩
  · intro s hs
    have hm : R.mapField η V = J := by funext r; exact R.map_unmap J (mem_univ _)
    have h := R.indexPairDensity_map hU hη hηR hV hV hs
    rw [he,hm] at h
    exact h.symm
  · intro s hs
    exact (congrArg (mfderiv I3 I3 (fromRight δ) (η s)).inverse hs).trans
      ((mfderiv I3 I3 (fromRight δ) (η s)).inverse.map_zero)
  · intro s hs
    have hv := R.velocity_map (hη.contMDiffAt (hU.mem_nhds hs)) (hηR hs)
    rw [he] at hv
    change (normalizedRight hδ).inner (η s) (velocity η s) (velocity η s) = _
    rw [hv,← congrFun he s]
    exact (R.metric (η s) (hηR hs) (velocity η s) (velocity η s)).symm
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma const_on_closed_of_deriv_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {a b : ℝ} (hab : a ≤ b) (hf : ∀ s ∈ Icc a b, HasDerivAt f 0 s) :
    ∀ s ∈ Icc a b, f s = f a := by
  intro s hs
  have hn := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hf r hr).hasDerivWithinAt) (C := 0) (by simp) (left_mem_Icc.mpr hab) hs
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using hn

lemma framed_closed_momentum (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (ht : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1) :
    ∃ p : TVec, ∀ s ∈ Icc a b, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p :=
  ⟨_,const_on_closed_of_deriv_zero hab
    (fun s hs => framed_momentum_hasDerivAt right hδ hU hγ (hsub hs) (ht s hs))⟩

lemma framed_unit_entry_zero_index (right : Bool) {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (h0 : γ 0 0 = 0) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  obtain ⟨p,hp⟩ := framed_closed_momentum right hδ hU hγ hL.le hsub hrc
  by_cases hc : ∃ c ∈ Ioo 0 L, deriv γ c 0 = 0
  · obtain ⟨c,hc,hvc⟩ := hc
    exact framed_turn_index right hδ hC hsmall (hB right) hU hsub hc hγ hJ hp h0 hrc hend hvc hr hunit
  · exact framed_monotone_index right hδ hU hL hsub hγ hJ hp hrc hr
      (Or.inl (Or.inl h0)) hend (fun s hs hzero => hc ⟨s,hs,hzero⟩) hunit

lemma unit_entry_index {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (h0 : γ 0 0 = 0 ∨ γ 0 0 = 1) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (normalizedNeck hδ) γ J J s := by
  rcases h0 with h0 | h0
  · exact framed_unit_entry_zero_index false hδ hC hsmall hB hU hL hsub hγ hJ h0 hrc hr hend hunit
  obtain ⟨η,V,hη,hV,hheight,hindex,hzero,henergy⟩ := right_frame_lift hδ hU hγ hJ
  have hV0 : J =ᶠ[𝓝 L] 0 → V =ᶠ[𝓝 L] 0 := by
    intro hz
    filter_upwards [hz] with s hs
    exact hzero s hs
  have hv := framed_unit_entry_zero_index true hδ hC hsmall hB hU hL hsub hη hV
    (by rw [hheight,h0]; ring)
    (fun s hs => by rw [hheight]; constructor <;> linarith [(hrc s hs).1,(hrc s hs).2])
    (fun s hs => by rw [hheight]; constructor <;> linarith [(hr s hs).1,(hr s hs).2])
    (by rcases hend with (hz|ho)|hJ0
        · exact Or.inl (Or.inr (by rw [hheight,hz]; ring))
        · exact Or.inl (Or.inl (by rw [hheight,ho]; ring))
        · exact Or.inr (hV0 hJ0))
    (fun s hs => (henergy s (hsub hs)).trans (hunit s hs))
  convert hv using 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact (hindex s (hsub (by simpa only [uIcc_of_le hL.le] using hs))).symm
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_affine_smoothField {γ J : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U) (a k : ℝ) :
    SmoothFieldOn (fun s => γ (a+k*s)) (fun s => J (a+k*s)) ((fun s : ℝ => a+k*s) ⁻¹' U) :=
  euclidean_smoothField ((euclidean_field_smooth hU hγ hJ).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn (fun _ hs => hs))
lemma affine_zero_germ {J : ℝ → E3} {a k s : ℝ} (hz : J =ᶠ[𝓝 (a+k*s)] 0) :
    (fun r => J (a+k*r)) =ᶠ[𝓝 s] 0 :=
  hz.comp_tendsto ((continuous_const.add (continuous_const.mul continuous_id)).tendsto s)
lemma euclidean_affine_speed (g : SmoothMetric E3) {γ : ℝ → E3} {a k s : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) :
    g.inner (γ (a+k*s)) (velocity (fun r => γ (a+k*r)) s) (velocity (fun r => γ (a+k*r)) s) =
      k^2 * g.inner (γ (a+k*s)) (velocity γ (a+k*s)) (velocity γ (a+k*s)) := by
  rw [euclidean_velocity,euclidean_velocity,affine_deriv hγ]
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ (a+k*s))
  change B (k • deriv γ (a+k*s)) (k • deriv γ (a+k*s)) = k^2 * B (deriv γ (a+k*s)) (deriv γ (a+k*s))
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem finite_unit_index {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ 0 0 = 0 ∨ γ 0 0 = 1) ∨ J =ᶠ[𝓝 0] 0)
    (hb : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (normalizedNeck hδ) γ J J s := by
  rcases ha with ha | ha
  · exact unit_entry_index hδ hC hsmall hB hU hL hsub hγ hJ ha hrc hr hb hunit
  rcases hb with hb | hb
  swap
  · exact framed_zero_endpoints_index false hδ (fun t ht p => (hB false t ht p).2.2.1)
      hU hγ (euclidean_field_smooth hU hγ.1 hJ) hL.le hsub hrc ha.eq_of_nhds hb.eq_of_nhds
  let A := fun s : ℝ => L+(-1)*s
  have hAc : Continuous A := continuous_const.add (continuous_const.mul continuous_id)
  have hclosed (s : ℝ) (hs : s ∈ Icc 0 L) : A s ∈ Icc 0 L := by
    dsimp only [A]; constructor <;> linarith [hs.1,hs.2]
  have hopen (s : ℝ) (hs : s ∈ Ioo 0 L) : A s ∈ Ioo 0 L := by
    dsimp only [A]; constructor <;> linarith [hs.1,hs.2]
  have hsub' : Icc 0 L ⊆ A ⁻¹' U := fun s hs => hsub (hclosed s hs)
  have hγ' := euclidean_affine_geodesic (normalizedNeck hδ) hU hγ L (-1)
  have hJ' := euclidean_affine_smoothField hU hγ.1 hJ L (-1)
  have hz : (fun s => J (A s)) =ᶠ[𝓝 L] 0 := by
    apply affine_zero_germ
    simpa only [neg_mul,one_mul,add_neg_cancel] using ha
  have hu := unit_entry_index hδ hC hsmall hB (hU.preimage hAc) hL hsub' hγ' hJ'
    (by simpa only [mul_zero,add_zero] using hb)
    (fun s hs => hrc _ (hclosed s hs)) (fun s hs => hr _ (hopen s hs)) (Or.inr hz)
    (fun s hs => by
      have hd : DifferentiableAt ℝ γ (L+(-1)*s) :=
        ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub' hs))).differentiableAt (by simp)
      rw [euclidean_affine_speed _ hd,hunit _ (hclosed s hs)]
      norm_num)
  have he := euclidean_affine_index_integral (normalizedNeck hδ) hU hγ.1 hJ
    (a := L) (k := -1) (u := 0) (v := L) (by norm_num) (fun s hs => hsub' (by simpa only [uIcc_of_le hL.le] using hs))
  rw [he] at hu
  simpa only [mul_zero,add_zero,neg_mul,one_mul,add_neg_cancel,
    intervalIntegral.integral_symm (a := L) (b := 0),neg_neg] using hu
end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_index_nonnegative_zero_velocity (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ)
    (hv : velocity γ s = 0) : 0 ≤ indexPairDensity g γ J J s := by
  rw [euclidean_velocity] at hv
  have hc : curvatureAlong g γ J s = 0 := by
    rw [euclidean_curvature,hv]
    change curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s) (J s) 0 0 = (0:E3)
    ext i
    simp [curvatureTerm]
  unfold indexPairDensity
  rw [hc]
  have hz : g.inner (γ s) (0 : TangentSpace I3 (γ s)) (J s) = 0 := by
    let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ s)
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (J s)) (map_zero B)
  rw [hz,sub_zero]
  exact inner_self_nonneg g _ _
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem finite_neck_index {δ C a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hrc : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo a b, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0)
    (hb : (γ b 0 = 0 ∨ γ b 0 = 1) ∨ J =ᶠ[𝓝 b] 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (normalizedNeck hδ) γ J J s := by
  let e := (normalizedNeck hδ).inner (γ a) (velocity γ a) (velocity γ a)
  have he : ∀ s ∈ Icc a b, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = e :=
    const_on_closed_of_deriv_zero hab.le (fun s hs => geodesic_speed_hasDerivAt _ hU hγ (hsub hs))
  have he0 : 0 ≤ e := inner_self_nonneg _ _ _
  by_cases hz : e = 0
  · apply intervalIntegral.integral_nonneg hab.le
    intro s hs
    apply euclidean_index_nonnegative_zero_velocity
    by_contra hv
    have hp := (normalizedNeck hδ).pos (γ s) (velocity γ s) hv
    rw [he s hs,hz] at hp
    exact lt_irrefl _ hp
  have hep : 0 < e := lt_of_le_of_ne he0 (Ne.symm hz)
  let k := 1/Real.sqrt e
  let L := (b-a)*Real.sqrt e
  have hroot : 0 < Real.sqrt e := Real.sqrt_pos.mpr hep
  have hk : 0 < k := one_div_pos.mpr hroot
  have hL : 0 < L := mul_pos (sub_pos.mpr hab) hroot
  have hends : a+k*L = b := by dsimp only [k,L]; field_simp; ring
  have hscale : k^2*e = 1 := by
    dsimp only [k]
    field_simp
    exact (Real.sq_sqrt he0).symm
  let A := fun s : ℝ => a+k*s
  have hAc : Continuous A := continuous_const.add (continuous_const.mul continuous_id)
  have hclosed (s : ℝ) (hs : s ∈ Icc 0 L) : A s ∈ Icc a b := by
    dsimp only [A]; constructor <;> nlinarith [mul_nonneg hk.le hs.1,mul_nonneg hk.le (sub_nonneg.mpr hs.2)]
  have hopen (s : ℝ) (hs : s ∈ Ioo 0 L) : A s ∈ Ioo a b := by
    dsimp only [A]; constructor <;> nlinarith [mul_pos hk hs.1,mul_pos hk (sub_pos.mpr hs.2)]
  have hsub' : Icc 0 L ⊆ A ⁻¹' U := fun s hs => hsub (hclosed s hs)
  have hγ' := euclidean_affine_geodesic (normalizedNeck hδ) hU hγ a k
  have hJ' := euclidean_affine_smoothField hU hγ.1 hJ a k
  have hleft : (γ (A 0) 0 = 0 ∨ γ (A 0) 0 = 1) ∨ (fun s => J (A s)) =ᶠ[𝓝 0] 0 := by
    rcases ha with ha | ha
    · exact Or.inl (by simpa only [A,mul_zero,add_zero] using ha)
    · exact Or.inr (affine_zero_germ (by simpa only [mul_zero,add_zero] using ha))
  have hright : (γ (A L) 0 = 0 ∨ γ (A L) 0 = 1) ∨ (fun s => J (A s)) =ᶠ[𝓝 L] 0 := by
    rcases hb with hb | hb
    · exact Or.inl (by simpa only [A,hends] using hb)
    · exact Or.inr (affine_zero_germ (by simpa only [hends] using hb))
  have hu := finite_unit_index hδ hC hsmall hB (hU.preimage hAc) hL hsub' hγ' hJ'
    (fun s hs => hrc _ (hclosed s hs)) (fun s hs => hr _ (hopen s hs)) hleft hright
    (fun s hs => by
      have hd : DifferentiableAt ℝ γ (a+k*s) :=
        ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub' hs))).differentiableAt (by simp)
      rw [euclidean_affine_speed _ hd,he _ (hclosed s hs)]
      exact hscale)
  rw [euclidean_affine_index_integral _ hU hγ.1 hJ hk.ne'
    (fun s hs => hsub' (by simpa only [uIcc_of_le hL.le] using hs)),mul_zero,add_zero,hends] at hu
  exact nonneg_of_mul_nonneg_right hu hk

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
open scoped ContDiff
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.finite_neck_index := @_root_.OAI.ThreeManifold.CompactMetric.finite_neck_index
