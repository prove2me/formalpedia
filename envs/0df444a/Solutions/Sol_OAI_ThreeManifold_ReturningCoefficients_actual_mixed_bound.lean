-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningCoefficients.actual_mixed_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:44:52.40755+00:00
-- url     : https://prove2.me/submissions/e7801c4e-d6b5-4db1-84a8-72000254f2d2

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L908-L963
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningCoefficients.actual_mixed_bound. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt
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

lemma pairing_matrix_sub (A B : TMat) (u v : TVec) :
    pairing (A - B) u v = pairing A u v - pairing B u v := by
  simp only [pairing, Matrix.sub_mulVec, dotProduct_sub]
lemma pairing_matrix_add (A B : TMat) (u v : TVec) :
    pairing (A + B) u v = pairing A u v + pairing B u v := by
  simp only [pairing, Matrix.add_mulVec, dotProduct_add]

lemma pairing_matrix_neg (A : TMat) (u v : TVec) :
    pairing (-A) u v = -pairing A u v := by
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

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

lemma constant_pairing_deriv {P : ℝ → TMat} {D : TMat} {u : ℝ}
    (hP : HasDerivAt P D u) (p q : TVec) :
    HasDerivAt (fun t => pairing (P t) p q) (pairing D p q) u := by
  simpa only [pairing, zero_dotProduct, Matrix.mulVec_zero, dotProduct_zero,
    zero_add, add_zero] using
    (pairing_hasDerivAt hP (hasDerivAt_const u p) (hasDerivAt_const u q))

lemma derivative_antitone {P₁ P₂ : ℝ → TMat} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt P₁ (P₂ t) t)
    (hc : ∀ t ∈ Icc 0 T, ∀ p, pairing (P₂ t) p p ≤ 0) (p : TVec) :
    AntitoneOn (fun t => pairing (P₁ t) p p) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
  · exact fun t ht => (constant_pairing_deriv (hd t ht) p p).continuousAt.continuousWithinAt
  · intro t ht
    exact (constant_pairing_deriv (hd t (interior_subset ht)) p p).hasDerivWithinAt
  · intro t ht
    exact hc t (interior_subset ht) p

lemma derivative_difference_psd {P₁ P₂ : ℝ → TMat} {T t : ℝ}
    (ht : t ∈ Icc 0 T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt P₁ (P₂ t) t)
    (hc : ∀ t ∈ Icc 0 T, ∀ p, pairing (P₂ t) p p ≤ 0) (p : TVec) :
    0 ≤ pairing (P₁ 0 - P₁ t) p p := by
  rw [pairing_matrix_sub]
  exact sub_nonneg.mpr (derivative_antitone hd hc p ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1)

lemma mixed_derivative_bound {D U : TMat} {a C δ p₁ : ℝ} {p e : TVec}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hD : Dᵀ = D) (hpos : ∀ q, 0 ≤ pairing D q q)
    (hee : pairing D e e ≤ 2 * C * δ)
    (hpp : pairing D p p ≤ δ * a * p₁ ^ 2)
    (hfirst : pairing (D + U) e p = δ * a * p₁) :
    |pairing U e p| ≤ (a + Real.sqrt (2 * C * a)) * δ * |p₁| := by
  have hcs := psd_cauchy hD hpos e p
  have hmul := mul_le_mul hee hpp (hpos p) (by positivity : 0 ≤ 2 * C * δ)
  have hs : (Real.sqrt (2 * C * a)) ^ 2 = 2 * C * a := Real.sq_sqrt (by positivity)
  have hsq : pairing D e p ^ 2 ≤ (Real.sqrt (2 * C * a) * δ * |p₁|) ^ 2 := by
    rw [mul_pow, mul_pow, hs, sq_abs]
    nlinarith [hcs, hmul]
  have hnorm : |pairing D e p| ≤ Real.sqrt (2 * C * a) * δ * |p₁| :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)
  have heq : pairing U e p = δ * a * p₁ - pairing D e p := by
    rw [pairing_matrix_add] at hfirst
    linarith
  rw [heq]
  calc
    |δ * a * p₁ - pairing D e p| ≤ |δ * a * p₁| + |pairing D e p| := abs_sub _ _
    _ ≤ δ * a * |p₁| + Real.sqrt (2 * C * a) * δ * |p₁| := by
      simpa only [abs_mul, abs_of_nonneg hδ, abs_of_nonneg ha] using
        add_le_add_right hnorm |δ * a * p₁|
    _ = _ := by ring

lemma mixed_variation_bound {P P₁ : ℝ → TMat} {T t K p₁ : ℝ} {p e : TVec}
    (hT : T ≤ 1) (hK : 0 ≤ K) (ht : t ∈ Icc 0 T)
    (hd : ∀ u ∈ Icc 0 T, HasDerivAt P (P₁ u) u)
    (hb : ∀ u ∈ Icc 0 T, |pairing (P₁ u) e p| ≤ K)
    (hp0 : pairing (P 0) e p = p₁) : |pairing (P t) e p - p₁| ≤ K := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (constant_pairing_deriv (hd u hu) e p).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hb u hu)
    (convex_Icc 0 T) (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
  rw [hp0, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
  exact hh.trans (mul_le_of_le_one_right hK (ht.2.trans hT))

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

lemma endpoint_pairing (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (coordinateCometric right δ 0) ![1, 0] p = p 0 := by
  rw [coordinateCometric_end (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  simp [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, A]

lemma endpoint_derivative_pairing (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) ![1, 0] p = δ * a 0 * p 0 := by
  rw [coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  simp [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma endpoint_derivative_qform (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) p p = δ * a 0 * p 0 ^ 2 := by
  rw [coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  simp only [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, add_zero]
  ring

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

lemma pairing_e_bound (D : TMat) {C : ℝ} (hC : 0 ≤ C)
    (hD : sqnorm (D *ᵥ e) ≤ C ^ 2) : |pairing D e e| ≤ C := by
  have hs : pairing D e e ^ 2 ≤ sqnorm (D *ᵥ e) := by
    simp only [pairing, dotProduct, Fin.sum_univ_two, e, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, zero_mul, add_zero, sqnorm]
    nlinarith [sq_nonneg ((D *ᵥ ![1, 0]) 1)]
  exact (sq_le_sq₀ (abs_nonneg _) hC).mp (by simpa only [sq_abs] using hs.trans hD)

lemma actual_mixed_bound {right : Bool} {δ T C : ℝ} {p : TVec}
    (hδ : 0 ≤ δ) (hC : 0 < C) (hT : T ∈ Icc 0 1)
    (hconc : ∀ t ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) q)
    (hder : ∀ t ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) t *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hforce : ∀ t ∈ Icc 0 T, 0 ≤ pairing (deriv (coordinateCometric right δ) t) p p) :
    ∀ t ∈ Icc 0 T,
      |pairing (coordinateCometric right δ t) e p - p 0| ≤
        (a 0 + Real.sqrt (2 * C * a 0)) * δ * |p 0| := by
  let R := coordinateCometric right δ
  have hsm : ContDiff ℝ ∞ R := coordinateCometric_smooth right δ
  have hsm1 := (contDiff_infty_iff_deriv.mp hsm).2
  have hdr (u : ℝ) : HasDerivAt R (deriv R u) u :=
    (hsm.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdr1 (u : ℝ) : HasDerivAt (deriv R) (deriv (deriv R) u) u :=
    (hsm1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc : ∀ u ∈ Icc 0 T, ∀ q, pairing (deriv (deriv R) u) q q ≤ 0 := by
    intro u hu q
    have hh := hconc u ⟨hu.1, hu.2.trans hT.2⟩ q
    change 0 ≤ pairing (-deriv (deriv R) u) q q at hh
    rw [pairing_matrix_neg] at hh
    linarith
  have hbound : ∀ u ∈ Icc 0 T, |pairing (deriv R u) e p| ≤
      (a 0 + Real.sqrt (2 * C * a 0)) * δ * |p 0| := by
    intro u hu
    let D := deriv R 0 - deriv R u
    have hpos (q : TVec) : 0 ≤ pairing D q q :=
      derivative_difference_psd hu (fun u _ => hdr1 u) hc q
    have hDs : Dᵀ = D := by
      dsimp only [D]
      rw [Matrix.transpose_sub, coordinateCometric_deriv_transpose,
        coordinateCometric_deriv_transpose]
    have hD0 : |pairing (deriv R 0) e e| ≤ C * δ :=
      pairing_e_bound _ (by positivity) (by
        simpa only [mul_pow] using hder 0 ⟨le_rfl, by norm_num⟩)
    have hDu : |pairing (deriv R u) e e| ≤ C * δ :=
      pairing_e_bound _ (by positivity) (by
        simpa only [mul_pow] using hder u ⟨hu.1, hu.2.trans hT.2⟩)
    have hee : pairing D e e ≤ 2 * C * δ := by
      dsimp only [D]
      rw [pairing_matrix_sub]
      have h0 := (abs_le.mp hD0).2
      have hu' := (abs_le.mp hDu).1
      linarith
    have hpp : pairing D p p ≤ δ * a 0 * p 0 ^ 2 := by
      dsimp only [D]
      rw [pairing_matrix_sub, endpoint_derivative_qform]
      linarith [hforce u hu]
    have hfirst : pairing (D + deriv R u) e p = δ * a 0 * p 0 := by
      dsimp only [D]
      rw [sub_add_cancel]
      exact endpoint_derivative_pairing right δ p
    exact mixed_derivative_bound (a_nonneg 0) hC.le hδ hDs hpos hee hpp hfirst
  intro t ht
  exact mixed_variation_bound hT.2
    (mul_nonneg (mul_nonneg (add_nonneg (a_nonneg 0) (Real.sqrt_nonneg _)) hδ) (abs_nonneg _)) ht (fun u _ => hdr u) hbound
    (endpoint_pairing right δ p)

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

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

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

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningCoefficients
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
open Neck Cometric Matrix


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningCoefficients.actual_mixed_bound := @_root_.OAI.ThreeManifold.ReturningCoefficients.actual_mixed_bound
