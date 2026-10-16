-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningPassage.returning_normal_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:58:37.232922+00:00
-- url     : https://prove2.me/submissions/a5fd3b54-42a9-4813-9b71-8bf6b1c898ec

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L2027-L2149
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningPassage.returning_normal_identity. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Cometric_coordinateCometric_end_deriv
import Theorems.Thm_OAI_ThreeManifold_Neck_energy_cometric_identity
import Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
import Theorems.Thm_OAI_ThreeManifold_Neck_normal_index_integral
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_momentumVelocity_hasDerivAt

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

lemma pairing_inverse {P Q : TMat} (hQP : Q * P = 1) (u v : TVec) :
    pairing Q u (P *ᵥ v) = dotProduct u v := by
  simp only [pairing, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]

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

lemma P_hermitian (δ t : ℝ) : (P δ t).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

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

lemma symmetric_derivative {R : ℝ → Mat2} {D : Mat2} {t : ℝ}
    (hR : ∀ u, (R u)ᵀ = R u) (hd : HasDerivAt R D t) : Dᵀ = D := by
  ext i j
  have hdi := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd j) i
  have hdj := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
  have he : (fun u => R u j i) = (fun u => R u i j) := by
    funext u
    exact congrFun (congrFun (hR u) i) j
  rw [he] at hdi
  exact hdi.unique hdj

lemma coordinateCometric_deriv_transpose (right : Bool) (δ t : ℝ) :
    (deriv (coordinateCometric right δ) t)ᵀ = deriv (coordinateCometric right δ) t :=
  symmetric_derivative (coordinateCometric_transpose right δ)
    (((coordinateCometric_smooth right δ).differentiable (by simp)).differentiableAt.hasDerivAt)

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

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

lemma turning_boundary_term (κ v : ℝ) (u z : TVec) :
    boundaryTerm !![-κ, 0; 0, 0] (v, u) (0, z) = κ * v * (z 0) ^ 2 / 2 := by
  simp only [boundaryTerm, zero_mul, add_zero, pairing, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, add_zero]
  ring

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

lemma momentumVelocity_pairing {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hdet : (coordinateCometric right δ (t s)).det ≠ 0) (W : Vec) :
    metric (metricInverse right δ (t s)) W (momentumVelocity right δ p t v s) =
      W.1 * v s + p ⬝ᵥ W.2 := by
  have hQP : metricInverse right δ (t s) * coordinateCometric right δ (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  simp only [momentumVelocity, metric, pairing_inverse hQP, dotProduct_comm]

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma returning_normal_identity {right : Bool} {δ L m : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L)
    (hdet : ∀ s ∈ Icc 0 L, (coordinateCometric right δ (t s)).det ≠ 0)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0) (hvL : v L = -v 0)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hwc : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0)
    (hlin : ∀ s ∈ Icc 0 L, HasDerivAt
      (fun r => metric (metricInverse right δ (t r)) (w r, z r)
        (momentumVelocity right δ p t v r)) m s) :
    (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v
      (fun r => (w r, z r)) (fun r => (w' r, z' r)) s) =
    (∫ s in (0 : ℝ)..L,
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s) +
      δ * a 0 * v 0 / 2 * ((z 0 0) ^ 2 + (z L 0) ^ 2) -
        (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by
  let R := coordinateCometric right δ
  let Q := metricInverse right δ
  let u := fun s => R (t s) *ᵥ p
  have htc := HasDerivAt.continuousOn ht
  have hvc := HasDerivAt.continuousOn hv
  have huc : ContinuousOn u (Icc 0 L) :=
    ((coordinateCometric_smooth right δ).continuous.matrix_mulVec continuous_const).comp_continuousOn htc
  have hRc : ContinuousOn (R ∘ t) (Icc 0 L) :=
    (coordinateCometric_smooth right δ).continuous.comp_continuousOn htc
  have hQa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ Q (t s) :=
    metricInverse_smoothAt (hdet s hs)
  have hQc : ContinuousOn (Q ∘ t) (Icc 0 L) := fun s hs =>
    (hQa s hs).continuousAt.comp_continuousWithinAt (htc s hs)
  have hAc : ContinuousOn (deriv Q ∘ t) (Icc 0 L) := fun s hs =>
    ((hQa s hs).derivWithin (m := ∞) (by simp)).continuousAt.comp_continuousWithinAt (htc s hs)
  have hBc : ContinuousOn (deriv (deriv Q) ∘ t) (Icc 0 L) := fun s hs =>
    (((hQa s hs).derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)).continuousAt.comp_continuousWithinAt (htc s hs)
  have hQP (s : ℝ) (hs : s ∈ Icc 0 L) : Q (t s) * R (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s hs))
  have hQs (s : ℝ) (_hs : s ∈ Icc 0 L) : (Q (t s))ᵀ = Q (t s) := metricInverse_transpose right δ (t s)
  have hPs (s : ℝ) (_hs : s ∈ Icc 0 L) : (R (t s))ᵀ = R (t s) := coordinateCometric_transpose right δ (t s)
  have hAs (s : ℝ) (_hs : s ∈ Icc 0 L) : (deriv Q (t s))ᵀ = deriv Q (t s) := metricInverse_deriv_transpose right δ (t s)
  have hBs (s : ℝ) (_hs : s ∈ Icc 0 L) : (deriv (deriv Q) (t s))ᵀ = deriv (deriv Q) (t s) := metricInverse_second_transpose right δ (t s)
  have hQd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt Q (deriv Q (t s)) (t s) :=
    ((hQa s hs).differentiableAt (by simp)).hasDerivAt
  have hAd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt (deriv Q) (deriv (deriv Q) (t s)) (t s) :=
    (((hQa s hs).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hTv (s : ℝ) (hs : s ∈ Icc 0 L) :
      HasDerivAt v ((1 / 2 : ℝ) * pairing (deriv Q (t s)) (u s) (u s)) s := by
    have hh := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (momentumVelocity_hasDerivAt (hdet s hs) (ht s hs) (hv s hs))
    simpa only [momentumVelocity, Function.comp_def, ContinuousLinearMap.coe_fst', gamma,
      Prod.fst_neg, neg_mul, neg_neg] using hh
  have hTu (s : ℝ) (hs : s ∈ Icc 0 L) :
      HasDerivAt u (-v s • (R (t s) *ᵥ (deriv Q (t s) *ᵥ u s))) s := by
    have hh := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (momentumVelocity_hasDerivAt (hdet s hs) (ht s hs) (hv s hs))
    apply hh.congr_deriv
    simp only [momentumVelocity, gamma, ContinuousLinearMap.coe_snd', Prod.snd_neg, neg_smul]
    dsimp only [u, R, Q]
    module
  have hnorm := normal_index_integral (a := 0) (c := L) (m := m)
    (by simpa only [uIcc_of_le hL.le] using hRc)
    (by simpa only [uIcc_of_le hL.le] using hQc)
    (by simpa only [uIcc_of_le hL.le] using hAc)
    (by simpa only [uIcc_of_le hL.le] using hBc)
    (by simpa only [uIcc_of_le hL.le] using hvc)
    (by simpa only [uIcc_of_le hL.le] using huc)
    (by simpa only [uIcc_of_le hL.le] using HasDerivAt.continuousOn hw)
    (by simpa only [uIcc_of_le hL.le] using HasDerivAt.continuousOn hz)
    (by simpa only [uIcc_of_le hL.le] using hwc)
    (by simpa only [uIcc_of_le hL.le] using hzc)
    (by simpa only [uIcc_of_le hL.le] using hQP)
    (by simpa only [uIcc_of_le hL.le] using hQs)
    (by simpa only [uIcc_of_le hL.le] using hPs)
    (by simpa only [uIcc_of_le hL.le] using hAs)
    (by simpa only [uIcc_of_le hL.le] using hBs)
    (by simpa only [uIcc_of_le hL.le] using ht)
    (by simpa only [uIcc_of_le hL.le] using hTv)
    (by simpa only [uIcc_of_le hL.le] using hTu)
    (by simpa only [uIcc_of_le hL.le] using hQd)
    (by simpa only [uIcc_of_le hL.le] using hAd)
    (by simpa only [uIcc_of_le hL.le] using hw)
    (by simpa only [uIcc_of_le hL.le] using hz)
    (by simpa only [uIcc_of_le hL.le, momentumVelocity, Q, u, R] using hlin)
  have hE (s : ℝ) (hs : s ∈ Icc 0 L) :
      coordinateEnergyDensity (Q (t s)) (deriv Q (t s)) (deriv (deriv Q) (t s))
        (v s, u s) (w s, z s) (w' s, z' s) =
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s := by
    rw [metricInverse_first (hdet s hs), metricInverse_second (hdet s hs)]
    rw [energy_cometric_identity (hQP s hs) (hPs s hs) (hQs s hs)
      (coordinateCometric_deriv_transpose right δ (t s))]
    dsimp only [energyDensity, forceDerivative, Q, metricInverse]
    ring
  have hEi : (∫ s in (0 : ℝ)..L, coordinateEnergyDensity (Q (t s))
      (deriv Q (t s)) (deriv (deriv Q) (t s)) (v s, u s) (w s, z s) (w' s, z' s)) =
      ∫ s in (0 : ℝ)..L, energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s := by
    apply intervalIntegral.integral_congr
    simpa only [uIcc_of_le hL.le, Set.EqOn] using hE
  have hm : L * m = p ⬝ᵥ (z L - z 0) := by
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := L)
      (by simpa only [uIcc_of_le hL.le] using hlin) intervalIntegrable_const
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hf
    rw [momentumVelocity_pairing (hdet L ⟨hL.le, le_rfl⟩),
      momentumVelocity_pairing (hdet 0 ⟨le_rfl, hL.le⟩), hwa, hwb, zero_mul, zero_add,
      zero_mul, zero_add, ← dotProduct_sub] at hf
    exact hf
  have hma : L * m ^ 2 = (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by
    rw [← hm]
    field_simp [hL.ne']
  have hdet0 : (coordinateCometric right δ 0).det ≠ 0 := by
    simpa only [h0] using hdet 0 ⟨le_rfl, hL.le⟩
  change (∫ s in (0 : ℝ)..L, normalDensity (R (t s)) (Q (t s)) (deriv Q (t s))
    (deriv (deriv Q) (t s)) (v s, u s) (w s, z s) (w' s, z' s)) = _
  rw [hnorm, hEi, sub_zero, hma, h0, h1, hwa, hwb, hvL,
    metricInverse_endpoint_deriv hdet0, turning_boundary_term, turning_boundary_term]
  ring

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

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningPassage.returning_normal_identity := @_root_.OAI.ThreeManifold.ReturningPassage.returning_normal_identity
