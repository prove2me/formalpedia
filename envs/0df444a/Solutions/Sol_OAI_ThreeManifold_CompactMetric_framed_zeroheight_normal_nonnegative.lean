-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.framed_zeroheight_normal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:09:20.859455+00:00
-- url     : https://prove2.me/submissions/81df2c47-e20d-4a71-8831-c57fd669e47e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L749-L835
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.framed_zeroheight_normal_nonnegative. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_normalizedRight_bilin
import Theorems.Thm_OAI_ThreeManifold_Neck_boundaryTerm_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_Neck_index_density_identity
import Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
import Theorems.Thm_OAI_ThreeManifold_ReturningCoefficients_psd_cauchy

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

lemma pairing_add_left (A : TMat) (u v w : TVec) :
    pairing A (u + v) w = pairing A u w + pairing A v w := by
  simp only [pairing, add_dotProduct]
lemma pairing_add_right (A : TMat) (u v w : TVec) :
    pairing A u (v + w) = pairing A u v + pairing A u w := by
  simp only [pairing, Matrix.mulVec_add, dotProduct_add]
lemma pairing_smul_right (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A u (r • v) = r * pairing A u v := by
  simp only [pairing, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

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

lemma metric_add_left (Q : TMat) (U V W : Vec) :
    metric Q (U + V) W = metric Q U W + metric Q V W := by
  simp only [metric, Prod.fst_add, Prod.snd_add, pairing_add_left]
  ring

lemma continuous_pairing : Continuous (fun p : TMat × TVec × TVec =>
    pairing p.1 p.2.1 p.2.2) := by
  unfold pairing Matrix.mulVec dotProduct
  fun_prop

lemma continuousOn_pairing {X : Type*} [TopologicalSpace X]
    {A : X → TMat} {u v : X → TVec} {S : Set X}
    (hA : ContinuousOn A S) (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun s => pairing (A s) (u s) (v s)) S :=
  continuous_pairing.comp_continuousOn (hA.prodMk (hu.prodMk hv))

lemma continuousOn_boundaryJet {X : Type*} [TopologicalSpace X] {S : Set X}
    {P A B : X → TMat} {T V Vdot : X → Vec}
    (hP : ContinuousOn P S) (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    (hT : ContinuousOn T S) (hV : ContinuousOn V S) (hVdot : ContinuousOn Vdot S) :
    ContinuousOn (fun s => boundaryJet (P s) (A s) (B s)
      (T s) (V s) (Vdot s)) S := by
  unfold boundaryJet
  have hS : ContinuousOn (fun s => A s * P s * A s) S := (hA.mul hP).mul hA
  exact ((((((continuousOn_const.mul (continuousOn_pairing hA hT.snd hT.snd)).mul
    (continuousOn_pairing hA hV.snd hV.snd)).sub
    (hT.fst.mul (continuousOn_pairing hA hVdot.snd hV.snd))).sub
    ((continuousOn_const.mul (hT.fst.pow 2)).mul (continuousOn_pairing hB hV.snd hV.snd))).add
    (hVdot.fst.mul (continuousOn_pairing hA hV.snd hT.snd))).add
    (hV.fst.mul (continuousOn_pairing hA hVdot.snd hT.snd))).add
    ((hV.fst.mul hT.fst).mul (continuousOn_pairing hB hV.snd hT.snd)) |>.sub
    ((hV.fst.mul hT.fst).mul (continuousOn_pairing hS hV.snd hT.snd))

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

lemma splitVector_hasDerivAt {f : ℝ → E3} {f' : E3} {s : ℝ}
    (hf : HasDerivAt f f' s) :
    HasDerivAt (fun r => splitVector (f r)) (splitVector f') s := by
  apply (hasDerivAt_pi.mp hf 0).prodMk
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hf 1
  · exact hasDerivAt_pi.mp hf 2

lemma split_neg (u : E3) : splitVector (-u) = -splitVector u := by
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> rfl

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

lemma metricInverse_second_transpose (right : Bool) (δ u : ℝ) :
    (deriv (deriv (metricInverse right δ)) u)ᵀ = deriv (deriv (metricInverse right δ)) u :=
  symmetric_total_deriv (metricInverse_deriv_transpose right δ) u

lemma metricInverse_smoothAt {right : Bool} {δ u : ℝ}
    (hdet : (coordinateCometric right δ u).det ≠ 0) :
    ContDiffAt ℝ ∞ (metricInverse right δ) u :=
  matrix_inverse_smoothAt (coordinateCometric_smooth right δ).contDiffAt hdet

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
lemma framed_velocity_equation (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => splitVector (deriv γ r))
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))) s := by
  have hd := ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).derivWithin (m := ∞) (by simp)
  have he := hγ.2 (OpenPartialHomeomorph.refl E3) (chart_mem_atlas E3 (0 : E3)) s hs (mem_univ _)
  change deriv (deriv γ) s + connectionTerm (framedNeck right hδ)
    (OpenPartialHomeomorph.refl E3) (γ s) (deriv γ s) (deriv γ s) = 0 at he
  rw [framedNeck_connection right hδ ht] at he
  have h := TorusNeck.splitVector_hasDerivAt (hd.differentiableAt (by simp)).hasDerivAt
  rw [eq_neg_of_add_eq_zero_left he,TorusNeck.split_neg,split_join] at h
  exact h

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

lemma zeroHeight_covariant_pair {P Q : TMat} (hQP : Q * P = 1) (hQ : Qᵀ = Q)
    (A : TMat) (v : ℝ) (u z zd : TVec) :
    metric Q ((0,zd) + gamma P A (v,u) (0,z)) (v,u) = pairing Q zd u := by
  rw [metric_add_left,metric_symm hQ (gamma P A (v,u) (0,z)),metric_gamma hQP]
  simp only [metric]
  ring

lemma zeroHeight_normalDensity {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (v : ℝ) (u z zd : TVec) :
    normalDensity P Q A B (v,u) (0,z) (0,zd) =
      pairing Q zd zd - (pairing Q zd u)^2 - boundaryJet P A B (v,u) (0,z) (0,zd) := by
  unfold normalDensity
  rw [index_density_identity hQP hQ hP hA hB,zeroHeight_covariant_pair hQP hQ]
  simp only [coordinateEnergyDensity]
  ring

lemma transverse_energy_nonneg {Q : TMat} (hQ : Qᵀ = Q)
    (hpos : ∀ z, 0 ≤ pairing Q z z) {v : ℝ} {u : TVec}
    (hu : metric Q (v,u) (v,u) = 1) (z : TVec) :
    0 ≤ pairing Q z z - (pairing Q z u)^2 := by
  have hc := psd_cauchy hQ hpos z u
  have hp := mul_nonneg (hpos z) (sq_nonneg v)
  change v * v + pairing Q u u = 1 at hu
  nlinarith

lemma zeroHeight_index_nonnegative
    {P Q A B : ℝ → TMat} {t v : ℝ → ℝ} {u z zd : ℝ → TVec} {a b : ℝ}
    (hab : a ≤ b)
    (hP : ContinuousOn (P ∘ t) (uIcc a b)) (hQ : ContinuousOn (Q ∘ t) (uIcc a b))
    (hA : ContinuousOn (A ∘ t) (uIcc a b)) (hB : ContinuousOn (B ∘ t) (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hu : ContinuousOn u (uIcc a b))
    (hz : ContinuousOn z (uIcc a b)) (hzd : ContinuousOn zd (uIcc a b))
    (hQP : ∀ s ∈ uIcc a b, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ uIcc a b, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ uIcc a b, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ uIcc a b, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ uIcc a b, (B (t s))ᵀ = B (t s))
    (hpos : ∀ s ∈ uIcc a b, ∀ q, 0 ≤ pairing (Q (t s)) q q)
    (hunit : ∀ s ∈ uIcc a b, metric (Q (t s)) (v s,u s) (v s,u s) = 1)
    (ht : ∀ s ∈ uIcc a b, HasDerivAt t (v s) s)
    (hvd : ∀ s ∈ uIcc a b, HasDerivAt v ((1/2:ℝ)*pairing (A (t s)) (u s) (u s)) s)
    (hud : ∀ s ∈ uIcc a b, HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hAd : ∀ s ∈ uIcc a b, HasDerivAt A (B (t s)) (t s))
    (hzd' : ∀ s ∈ uIcc a b, HasDerivAt z (zd s) s)
    (hboundary : boundaryTerm (A (t b)) (v b,u b) (0,z b) ≤
      boundaryTerm (A (t a)) (v a,u a) (0,z a)) :
    0 ≤ ∫ s in a..b, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s,u s) (0,z s) (0,zd s) := by
  let e := fun s => pairing (Q (t s)) (zd s) (zd s) - (pairing (Q (t s)) (zd s) (u s))^2
  let j := fun s => boundaryJet (P (t s)) (A (t s)) (B (t s)) (v s,u s) (0,z s) (0,zd s)
  have he : ContinuousOn e (uIcc a b) :=
    (continuousOn_pairing hQ hzd hzd).sub ((continuousOn_pairing hQ hzd hu).pow 2)
  have hj : ContinuousOn j (uIcc a b) := continuousOn_boundaryJet hP hA hB
    (hv.prodMk hu) (continuousOn_const.prodMk hz) (continuousOn_const.prodMk hzd)
  have hd : ∀ s ∈ uIcc a b, HasDerivAt
      (fun r => boundaryTerm (A (t r)) (v r,u r) (0,z r)) (j s) s := by
    intro s hs
    exact boundaryTerm_hasDerivAt (hPs s hs) (hAs s hs) (hBs s hs)
      (hAd s hs) (ht s hs) (hvd s hs) (hud s hs) (hasDerivAt_const s 0) (hzd' s hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hj.intervalIntegrable
  have heq : (∫ s in a..b, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s,u s) (0,z s) (0,zd s)) = (∫ s in a..b, e s) - (∫ s in a..b, j s) := by
    rw [← intervalIntegral.integral_sub he.intervalIntegrable hj.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro s hs
    exact zeroHeight_normalDensity (hQP s hs) (hQs s hs) (hPs s hs) (hAs s hs) (hBs s hs) _ _ _ _
  rw [heq,hFTC]
  have hen : 0 ≤ ∫ s in a..b, e s := by
    apply intervalIntegral.integral_nonneg hab
    intro s hs
    have hs' : s ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hs
    exact transverse_energy_nonneg (hQs s hs') (hpos s hs') (hunit s hs') _
  linarith
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

lemma framed_metric_velocity_equations (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (htr : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => deriv γ r 0)
      ((1/2:ℝ)*pairing (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)).2 (splitVector (deriv γ s)).2) s ∧
    HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-deriv γ s 0 • (coordinateCometric right δ (γ s 0) *ᵥ
        (deriv (metricInverse right δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
  have hvel := framed_velocity_equation right hδ hU hγ hs htr
  constructor
  · have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => deriv γ r 0)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
    convert h using 1
    simp only [gamma,Prod.fst_neg]
    ring
  · have h := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at h
    convert h using 1
    ext i
    simp only [gamma,Prod.snd_neg,Pi.neg_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul,splitVector]
    ring

lemma framed_zeroheight_normal_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ W : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hW : ContDiffOn ℝ ∞ W U) (hW0 : ∀ s ∈ U, W s 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (W b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a)) (splitVector (W a))) :
    0 ≤ ∫ s in a..b, normalDensity (coordinateCometric right δ (γ s 0))
      (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
      (deriv (deriv (metricInverse right δ)) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (W s)) (splitVector (deriv W s)) := by
  let t := fun s => γ s 0
  let v := fun s => deriv γ s 0
  let u := fun s => (splitVector (deriv γ s)).2
  let z := fun s => (splitVector (W s)).2
  let zd := fun s => (splitVector (deriv W s)).2
  have hsubs : uIcc a b ⊆ U := by rwa [uIcc_of_le hab]
  have htrs : ∀ s ∈ uIcc a b, γ s 0 ∈ Icc (0:ℝ) 1 := by rwa [uIcc_of_le hab]
  have hgc (s : ℝ) (hs : s ∈ uIcc a b) := (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsubs hs))
  have hwc (s : ℝ) (hs : s ∈ uIcc a b) := hW.contDiffAt (hU.mem_nhds (hsubs hs))
  have ht (s : ℝ) (hs : s ∈ uIcc a b) : HasDerivAt t (v s) s :=
    hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0
  have hP : ContinuousOn (coordinateCometric right δ ∘ t) (uIcc a b) :=
    fun s hs => ((coordinateCometric_smooth right δ).continuous.continuousAt.comp (ht s hs).continuousAt).continuousWithinAt
  have hQ : ContinuousOn (metricInverse right δ ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (metricInverse right δ) (t s) := (metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hA : ContinuousOn (deriv (metricInverse right δ) ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (deriv (metricInverse right δ)) (t s) := ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hB : ContinuousOn (deriv (deriv (metricInverse right δ)) ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (deriv (deriv (metricInverse right δ))) (t s) := (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hTc : ContinuousOn (fun s => splitVector (deriv γ s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp ((hgc s hs).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hWc : ContinuousOn (fun s => splitVector (W s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp (hwc s hs).continuousAt).continuousWithinAt
  have hDc : ContinuousOn (fun s => splitVector (deriv W s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp ((hwc s hs).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hw0 (s : ℝ) (hs : s ∈ uIcc a b) : splitVector (W s) = (0,z s) := by
    change (W s 0,z s) = _
    rw [hW0 s (hsubs hs)]
  have hd0 (s : ℝ) (hs : s ∈ uIcc a b) : splitVector (deriv W s) = (0,zd s) := by
    have hgerm : (fun r => W r 0) =ᶠ[nhds s] (fun _ => (0:ℝ)) := by
      filter_upwards [hU.mem_nhds (hsubs hs)] with r hr
      exact hW0 r hr
    have hh := hasDerivAt_pi.mp ((hwc s hs).differentiableAt (by simp)).hasDerivAt 0
    have hd : deriv W s 0 = 0 := hh.deriv.symm.trans (hgerm.deriv_eq.trans (deriv_const s 0))
    change (deriv W s 0,zd s) = _
    rw [hd]
  have hbnd : boundaryTerm (deriv (metricInverse right δ) (t b)) (v b,u b) (0,z b) ≤
      boundaryTerm (deriv (metricInverse right δ) (t a)) (v a,u a) (0,z a) := by
    rw [hw0 a left_mem_uIcc,hw0 b right_mem_uIcc] at hboundary
    exact hboundary
  have hbound := zeroHeight_index_nonnegative hab hP hQ hA hB hTc.fst hTc.snd hWc.snd hDc.snd
    (fun s hs => frame_QP right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))
    (fun s _ => metricInverse_transpose right δ (t s))
    (fun s _ => coordinateCometric_transpose right δ (t s))
    (fun s _ => metricInverse_deriv_transpose right δ (t s))
    (fun s _ => metricInverse_second_transpose right δ (t s))
    (fun s hs q => ?_) (fun s hs => ?_) ht
    (fun s hs => (framed_metric_velocity_equations right hδ hU hγ (hsubs hs) (htrs s hs)).1)
    (fun s hs => (framed_metric_velocity_equations right hδ hU hγ (hsubs hs) (htrs s hs)).2)
    (fun s hs => (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt)
    (fun s hs => (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (splitVector_hasDerivAt ((hwc s hs).differentiableAt (by simp)).hasDerivAt)) hbnd
  · convert hbound using 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hw0 s hs,hd0 s hs]
  · have hp := (coordinateCometric_posDef (fun q => (frame_elliptic right ⟨hδ.1.le,hδ.2⟩ (htrs s hs) q).1)).inv.posSemidef
    have hh := hp.dotProduct_mulVec_nonneg q
    simp only [star_trivial] at hh
    change 0 ≤ pairing (metricInverse right δ (γ s 0)) q q at hh
    exact hh
  · have hh := hunit s (by simpa only [uIcc_of_le hab] using hs)
    rw [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [(htrs s hs).1],by linarith [(htrs s hs).2]⟩] at hh
    exact hh

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
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.framed_zeroheight_normal_nonnegative := @_root_.OAI.ThreeManifold.CompactMetric.framed_zeroheight_normal_nonnegative
