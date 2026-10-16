-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.framed_truncated_return_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:59:58.033988+00:00
-- url     : https://prove2.me/submissions/3e69e809-1ab8-424e-bbe9-98b64f5162d7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L121-L210
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.framed_truncated_return_index. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_scalar_equation
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_normalizedRight_bilin
import Theorems.Thm_OAI_ThreeManifold_Neck_curvatureTerm_product
import Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_finite_turn_completion
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_truncated_return_nonnegative

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

lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

lemma metric_symm {Q : TMat} (hQ : Qᵀ = Q) (U V : Vec) :
    metric Q U V = metric Q V U := by
  rw [metric, metric, pairing_symm hQ]
  ring

lemma pairing_mulVec_left (A L : TMat) (u v : TVec) :
    pairing A (L *ᵥ u) v = pairing (Lᵀ * A) u v := by
  unfold pairing
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

lemma pairing_mulVec_right (A L : TMat) (u v : TVec) :
    pairing A u (L *ᵥ v) = pairing (A * L) u v := by
  simp only [pairing, Matrix.mulVec_mulVec]

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

lemma blockMatrix_mul (P Q : TMat) :
    blockMatrix P * blockMatrix Q = blockMatrix (P * Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
lemma blockMatrix_one : blockMatrix (1 : TMat) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
lemma blockMatrix_inverse {P Q : TMat} (hQP : Q * P = 1) :
    (blockMatrix Q)⁻¹ = blockMatrix P := by
  apply Matrix.inv_eq_right_inv
  rw [blockMatrix_mul, hQP, blockMatrix_one]

lemma block_entry_hasDerivAt {Q : ℝ → TMat} {A : TMat} {s : ℝ}
    (hQ : HasDerivAt Q A s) (i j : Fin 3) :
    HasDerivAt (fun r => blockMatrix (Q r) i j) (blockJet A i j) s := by
  have h (k l : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ k) l
  fin_cases i <;> fin_cases j <;>
    simp only [blockMatrix, blockJet] <;>
    first | exact hasDerivAt_const _ _ | exact h _ _

lemma coordPartial_block {Q : ℝ → TMat} {A : TMat} {x : E3}
    (hQ : HasDerivAt Q A (x 0)) (i j k : Fin 3) :
    coordPartial (fun y => blockMatrix (Q (y 0)) i j) x k =
      (if k = 0 then 1 else 0) * blockJet A i j := by
  have h := (block_entry_hasDerivAt hQ i j).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt (fun y : E3 => blockMatrix (Q (y 0)) i j) _ x at h
  change (fderiv ℝ (fun y : E3 => blockMatrix (Q (y 0)) i j) x) (basisVector k) = _
  rw [h.fderiv]
  fin_cases k <;> simp [basisVector, ContinuousLinearMap.comp_apply]

lemma coordPartial_congr_germ {f h : E3 → ℝ} {x : E3}
    (heq : f =ᶠ[nhds x] h) (i : Fin 3) :
    coordPartial f x i = coordPartial h x i := by
  rw [coordPartial, coordPartial, heq.fderiv_eq]

lemma christoffel_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (i j k : Fin 3) :
    christoffel g c x i j k = (1 / 2 : ℝ) * ∑ l : Fin 3,
      blockMatrix P i l *
        ((if j = 0 then 1 else 0) * blockJet A l k +
         (if k = 0 then 1 else 0) * blockJet A l j -
         (if l = 0 then 1 else 0) * blockJet A j k) := by
  have hentry (a b d : Fin 3) :
      coordPartial (fun y => metricMatrix g c y a b) x d =
        (if d = 0 then 1 else 0) * blockJet A a b := by
    rw [coordPartial_congr_germ
      (Filter.Eventually.mono hg (fun _ h => congrFun (congrFun h a) b))]
    exact coordPartial_block hQ a b d
  rw [christoffel, hg.eq_of_nhds, blockMatrix_inverse hQP]
  simp only [hentry]

lemma connectionTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (hA : Aᵀ = A) (u v : E3) :
    connectionTerm g c x u v =
      joinVector (gamma P A (splitVector u) (splitVector v)) := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  ext i
  fin_cases i <;>
    simp [connectionTerm, christoffel_product g c hg hQ hQP,
      blockMatrix, blockJet, joinVector, gamma, splitVector, pairing,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10] <;> ring

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

lemma split_add (u v : E3) : splitVector (u + v) = splitVector u + splitVector v := by
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> rfl

lemma splitVector_hasDerivAt {f : ℝ → E3} {f' : E3} {s : ℝ}
    (hf : HasDerivAt f f' s) :
    HasDerivAt (fun r => splitVector (f r)) (splitVector f') s := by
  apply (hasDerivAt_pi.mp hf 0).prodMk
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hf 1
  · exact hasDerivAt_pi.mp hf 2

lemma splitVector_smooth : ContDiff ℝ ∞ splitVector := by
  apply (contDiff_apply ℝ ℝ 0).prodMk
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 1
  · exact contDiff_apply ℝ ℝ 2

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

lemma sqnorm_e : sqnorm e = 1 := by norm_num [e, sqnorm]

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

lemma metricInverse_deriv_transpose (right : Bool) (δ u : ℝ) :
    (deriv (metricInverse right δ) u)ᵀ = deriv (metricInverse right δ) u :=
  symmetric_total_deriv (metricInverse_transpose right δ) u

lemma metricInverse_smoothAt {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    ContDiffAt ℝ ∞ (metricInverse right δ) u :=
  matrix_inverse_smoothAt (coordinateCometric_smooth right δ).contDiffAt hdet

lemma metricInverse_first {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    deriv (metricInverse right δ) u =
      -metricInverse right δ u * deriv (coordinateCometric right δ) u * metricInverse right δ u :=
  matrix_inverse_first_deriv (coordinateCometric_smooth right δ) hdet

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

lemma framedNeck_bilin (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) (u v : E3) :
    (framedNeck right hδ).inner x u v =
      metric (metricInverse right δ (x 0)) (splitVector u) (splitVector v) := by
  cases right
  · exact normalizedNeck_bilin hδ hx u v
  · exact normalizedRight_bilin hδ hx u v

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
lemma framedNeck_connection (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) (u v : E3) :
    connectionTerm (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) x u v =
      joinVector (gamma (coordinateCometric right δ (x 0)) (deriv (metricInverse right δ) (x 0))
        (splitVector u) (splitVector v)) :=
  connectionTerm_product _ _ (framedNeck_matrix_germ right hδ hx)
    ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hx)).differentiableAt (by simp)).hasDerivAt
    (frame_QP right ⟨hδ.1.le,hδ.2⟩ hx) (metricInverse_deriv_transpose right δ (x 0)) u v
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma framed_velocity_torus (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (splitVector (deriv γ s)).2 = coordinateCometric right δ (γ s 0) *ᵥ p := by
  rw [← hp,mulVec_mulVec,frame_PQ right ⟨hδ.1.le,hδ.2⟩ ht,one_mulVec]

lemma framed_energy_identity (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) =
      potential right δ p (γ s 0) + (deriv γ s 0)^2 := by
  rw [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩]
  unfold Neck.metric
  rw [framed_velocity_torus right hδ ht hp,pairing_mulVec_left,pairing_mulVec_right,
    coordinateCometric_transpose,frame_PQ right ⟨hδ.1.le,hδ.2⟩ ht,Matrix.one_mul]
  simp only [potential,splitVector]
  ring

lemma framed_P_hasDerivAt (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    HasDerivAt (coordinateCometric right δ)
      (-coordinateCometric right δ t * deriv (metricInverse right δ) t * coordinateCometric right δ t) t := by
  have he : -coordinateCometric right δ t * deriv (metricInverse right δ) t * coordinateCometric right δ t =
      deriv (coordinateCometric right δ) t := by
    rw [metricInverse_first (frame_det_ne right hδ ht)]
    simp only [Matrix.neg_mul,Matrix.mul_neg,neg_neg,← Matrix.mul_assoc,
      frame_PQ right hδ ht,Matrix.one_mul]
    rw [Matrix.mul_assoc,frame_QP right hδ ht,Matrix.mul_one]
  rw [he]
  exact ((coordinateCometric_smooth right δ).differentiable (by simp) t).hasDerivAt
lemma framedNeck_curvature (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) (u v w : E3) :
    curvatureTerm (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) x u v w =
      joinVector (curvatureJet (coordinateCometric right δ (x 0)) (deriv (metricInverse right δ) (x 0))
        (deriv (deriv (metricInverse right δ)) (x 0)) (splitVector u) (splitVector v) (splitVector w)) := by
  apply curvatureTerm_product _ _ (framedNeck_matrix_germ right hδ hx)
  · have hc : ContinuousAt (fun t => (coordinateCometric right δ t).det) (x 0) :=
      (coordinateCometric_smooth right δ).continuous.matrix_det.continuousAt
    filter_upwards [hc.eventually_ne (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hx)] with t ht
    exact ⟨((metricInverse_smoothAt ht).differentiableAt (by simp)).hasDerivAt,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht),metricInverse_deriv_transpose right δ t⟩
  · exact framed_P_hasDerivAt right ⟨hδ.1.le,hδ.2⟩ hx
  · exact (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hx)).derivWithin
      (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt

lemma framedNeck_covariant (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (γ J : ℝ → E3)
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    covariantDerivative (framedNeck right hδ) γ J s = deriv J s +
      joinVector (gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s))) := by
  unfold covariantDerivative
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
    (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s = _
  rw [euclidean_fieldCoordinates,alongDerivative,framedNeck_connection right hδ ht]

lemma framedNeck_curvatureAlong (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (γ J : ℝ → E3)
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    curvatureAlong (framedNeck right hδ) γ J s =
      joinVector (curvatureJet (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (J s))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
    (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s) = _
  rw [euclidean_fieldCoordinates,framedNeck_curvature right hδ ht]

lemma framedNeck_index_density (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    indexPairDensity (framedNeck right hδ) γ J J s =
      normalDensity (coordinateCometric right δ (γ s 0)) (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s))
        (splitVector (deriv J s)) +
      ((framedNeck right hδ).inner (γ s) (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2 := by
  rw [euclidean_velocity,framedNeck_covariant right hδ γ J ht]
  unfold indexPairDensity
  rw [framedNeck_covariant right hδ γ J ht,
    framedNeck_curvatureAlong right hδ γ J ht]
  have hm : ∀ u v : E3, (framedNeck right hδ).inner (γ s) u v = Neck.metric (metricInverse right δ (γ s 0)) (splitVector u) (splitVector v) :=
    framedNeck_bilin right hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simp only [hm,
    TorusNeck.split_add,split_join,normalDensity]
  rw [metric_symm (metricInverse_transpose right δ (γ s 0)) (curvatureJet _ _ _ _ _ _) (splitVector (J s))]
  ring
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma split_deriv {J : ℝ → E3} {s : ℝ} (hJ : DifferentiableAt ℝ J s) :
    deriv (fun r => splitVector (J r)) s = splitVector (deriv J s) :=
  (TorusNeck.splitVector_hasDerivAt hJ.hasDerivAt).deriv

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients
lemma framed_return_density (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Ioo (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) (hJ : DifferentiableAt ℝ J s) :
    returnNormalDensity right δ p (fun r => γ r 0) (fun r => deriv γ r 0)
      (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s =
    indexPairDensity (framedNeck right hδ) γ J J s -
      ((framedNeck right hδ).inner (γ s) (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2 := by
  rw [framedNeck_index_density right hδ ⟨ht.1.le,ht.2.le⟩,add_sub_cancel_right]
  have he : momentumVelocity right δ p (fun r => γ r 0) (fun r => deriv γ r 0) s =
      splitVector (deriv γ s) := by
    apply Prod.ext
    · rfl
    · exact (framed_velocity_torus right hδ ⟨ht.1.le,ht.2.le⟩ hp).symm
  rw [returnNormalDensity,he,split_deriv hJ]

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

theorem framed_truncated_return_index (right : Bool) {δ C L c : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3 * C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hc : c ∈ Ioo 0 L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0)
    (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hvc : deriv γ c 0 = 0)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hstar : 1/4 < γ c 0)
    (henergy : ∀ s ∈ Icc 0 L,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  have hL : 0 < L := hc.1.trans hc.2
  have hgc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ γ s :=
    (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))
  have hJc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ J s :=
    (euclidean_field_smooth hU hγ.1 hJ).contDiffAt (hU.mem_nhds (hsub hs))
  have hVa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ (fun r => splitVector (J r)) s := by
    exact (TorusNeck.splitVector_smooth.contDiffAt.comp s (hJc s hs))
  let f := indexPairDensity (framedNeck right hδ) γ J J
  let q := fun s => ((framedNeck right hδ).inner (γ s)
      (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2
  have hfi : IntervalIntegrable f volume 0 L :=
    ((indexPairDensity_smooth _ hU hγ.1 hJ hJ).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have hqi : IntervalIntegrable q volume 0 L :=
    (((intrinsic_pairing_smooth _ hU hγ.1 (covariantDerivative_smooth _ hU hγ.1 hJ)
      (velocity_smooth hU hγ.1)).pow 2).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have hnormalI : IntervalIntegrable (returnNormalDensity right δ p (fun r => γ r 0)
      (fun r => deriv γ r 0) (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r)))) volume 0 L := by
    apply (hfi.sub hqi).congr_ae
    apply (ae_restrict_mem measurableSet_uIoc).mono
    intro s hs
    rw [uIoc_of_le hL.le] at hs
    have hi := framedNeck_index_density right hδ (J := J) (hrc s (Ioc_subset_Icc_self hs))
    have he : momentumVelocity right δ p (fun r => γ r 0) (fun r => deriv γ r 0) s = splitVector (deriv γ s) := by
      apply Prod.ext
      · rfl
      · exact (framed_velocity_torus right hδ (hrc s (Ioc_subset_Icc_self hs)) (hp s (Ioc_subset_Icc_self hs))).symm
    dsimp only [f,q]
    rw [framedNeck_index_density right hδ (hrc s (Ioc_subset_Icc_self hs)),add_sub_cancel_right]
    rw [returnNormalDensity,he,split_deriv ((hJc s (Ioc_subset_Icc_self hs)).differentiableAt (by simp))]
  have hcut : L < 2*c → (fun r => splitVector (J r)) =ᶠ[𝓝 L] 0 := by
    intro hLC
    have hcomp := PassageDynamics.finite_turn_completion (force_smooth right δ p) hc
      (fun s hs => hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0)
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs)) hvc h0 hr
    simp only [sub_zero] at hcomp
    have hheight := hcomp.2.2.2.2.2 L ⟨hL,hLC⟩
    rw [hcomp.2.1 (right_mem_Icc.mpr hL.le)] at hheight
    change γ L 0 ∈ Ioo (0:ℝ) 1 at hheight
    rcases hend with (hz | ho) | hz
    · rw [hz] at hheight
      exact (lt_irrefl 0 hheight.1).elim
    · rw [ho] at hheight
      exact (lt_irrefl 1 hheight.2).elim
    · filter_upwards [hz] with s hs
      simp [hs,splitVector]
  have hbound : 0 ≤ ∫ s in (0:ℝ)..L,
      returnNormalDensity right δ p (fun r => γ r 0) (fun r => deriv γ r 0)
        (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s := by
    apply truncated_return_nonnegative (right := right) (p := p)
      (t := fun r => γ r 0) (v := fun r => deriv γ r 0) hC hsmall (fun u hu q => (hb u hu q).1)
      (fun u hu => ?_) (fun u hu q => (hb u hu q).2.2.1)
      (fun u hu => (hb u hu p).2.2.2) hc
      (fun s hs => hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0)
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s (hgc s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s
        ((hgc s hs).derivWithin (m := ∞) (by simp)))
      h0 hr hvc hstar (fun s hs => (framed_energy_identity right hδ (hrc s hs) (hp s hs)).symm.trans (henergy s hs)) hVa hcut hnormalI
    simpa only [sqnorm_e,mul_one] using (hb u hu e).2.1
  have he : (∫ s in (0:ℝ)..L, returnNormalDensity right δ p (fun r => γ r 0)
      (fun r => deriv γ r 0) (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s) =
      ∫ s in (0:ℝ)..L, (f s - q s) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le hL.le]
    intro s hs
    exact framed_return_density right hδ (hr s hs) (hp s (Ioo_subset_Icc_self hs))
      ((hJc s (Ioo_subset_Icc_self hs)).differentiableAt (by simp))
  rw [he,intervalIntegral.integral_sub hfi hqi] at hbound
  have hq : 0 ≤ ∫ s in (0:ℝ)..L, q s := intervalIntegral.integral_nonneg hL.le (fun s _ => sq_nonneg _)
  linarith
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
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.framed_truncated_return_index := @_root_.OAI.ThreeManifold.CompactMetric.framed_truncated_return_index
