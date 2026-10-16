-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningPassage.returning_arbitrary_field_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:00:13.049312+00:00
-- url     : https://prove2.me/submissions/a4d8d43e-a8b3-4445-b953-4e26dd77e09c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L2265-L2328
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningPassage.returning_arbitrary_field_nonnegative. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Neck_matrix_inverse_smoothAt
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_actual_returning_energy_bound
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_momentumVelocity_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_dynamics
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_normal_identity

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

lemma a_zero : a 0 = Real.exp (-(3 : ℝ) / 2) := by norm_num [a_formula]

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

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

lemma pairing_add_left (A : TMat) (u v w : TVec) :
    pairing A (u + v) w = pairing A u w + pairing A v w := by
  simp only [pairing, add_dotProduct]
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

lemma metric_add_left (Q : TMat) (U V W : Vec) :
    metric Q (U + V) W = metric Q U W + metric Q V W := by
  simp only [metric, Prod.fst_add, Prod.snd_add, pairing_add_left]
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

lemma P_hermitian (δ t : ℝ) : (P δ t).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

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

lemma metric_smul_left (Q : TMat) (r : ℝ) (U V : Vec) :
    metric Q (r • U) V = r * metric Q U V := by
  simp only [metric, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pairing_smul_left]
  ring

lemma gamma_add_right (P A : TMat) (T U V : Vec) :
    gamma P A T (U + V) = gamma P A T U + gamma P A T V := by
  apply Prod.ext
  · simp only [gamma, Prod.fst_add, Prod.snd_add, pairing_add_right]
    ring
  · simp only [gamma, Prod.fst_add, Prod.snd_add, Matrix.mulVec_add,
      smul_add, add_smul]
    module

lemma gamma_smul_right (P A : TMat) (r : ℝ) (T V : Vec) :
    gamma P A T (r • V) = r • gamma P A T V := by
  apply Prod.ext
  · simp only [gamma, Prod.smul_fst, Prod.smul_snd, pairing_smul_right, smul_eq_mul]
    ring
  · simp only [gamma, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul]
    module

lemma covariant_gauge (P A : TMat) (T V D : Vec) (h h' : ℝ) :
    (D + h' • T - h • gamma P A T T) + gamma P A T (V + h • T) =
      (D + gamma P A T V) + h' • T := by
  rw [gamma_add_right, gamma_smul_right]
  module

lemma curvature_contraction_gauge {P Q A B : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B) (V T : Vec) (h : ℝ) :
    metric Q (V + h • T) (curvatureJet P A B (V + h • T) T T) =
      metric Q V (curvatureJet P A B V T T) := by
  rw [curvature_contraction hQP hP hA hB, curvature_contraction hQP hP hA hB]
  have hw : (V + h • T).1 • T.2 - T.1 • (V + h • T).2 = V.1 • T.2 - T.1 • V.2 := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    module
  rw [hw]
  simp only [Prod.snd_add, Prod.smul_snd, pairing_add_left, pairing_add_right,
    pairing_smul_left, pairing_smul_right, pairing_symm hA T.2 V.2]
  ring

lemma normalDensity_gauge {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (T V D : Vec) (hunit : metric Q T T = 1) (h h' : ℝ) :
    normalDensity P Q A B T (V + h • T) (D + h' • T - h • gamma P A T T) =
      normalDensity P Q A B T V D := by
  simp only [normalDensity, covariant_gauge,
    curvature_contraction_gauge hQP hP hA hB, metric_add_left, metric_add_right,
    metric_smul_left, metric_smul_right, metric_symm hQ T D,
    metric_symm hQ T (gamma P A T V), hunit]
  ring

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

lemma turningAffine_zero (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) :
    turningAffine L v₀ V T Q 0 = metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀ := by
  simp [turningAffine]

lemma turningAffine_end {L : ℝ} (hL : L ≠ 0) (v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) :
    turningAffine L v₀ V T Q L = metric (Q L) (V L) (T L) + (V L).1 / v₀ := by
  simp [turningAffine, hL]

lemma turningField_zero {L v₀ : ℝ} (hv₀ : v₀ ≠ 0) (V T : ℝ → Vec)
    (Q : ℝ → TMat) (hT : (T 0).1 = v₀) :
    (turningField L v₀ V T Q 0).1 = 0 := by
  simp only [turningField, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
    turningChange, turningAffine_zero, hT]
  field_simp
  ring

lemma turningField_end {L v₀ : ℝ} (hL : L ≠ 0) (hv₀ : v₀ ≠ 0) (V T : ℝ → Vec)
    (Q : ℝ → TMat) (hT : (T L).1 = -v₀) :
    (turningField L v₀ V T Q L).1 = 0 := by
  simp only [turningField, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
    turningChange, turningAffine_end hL, hT]
  field_simp
  ring

lemma turningField_tangential {L v₀ s : ℝ} (V T : ℝ → Vec) (Q : ℝ → TMat)
    (hunit : metric (Q s) (T s) (T s) = 1) :
    metric (Q s) (turningField L v₀ V T Q s) (T s) = turningAffine L v₀ V T Q s := by
  simp only [turningField, turningChange, metric_add_left, metric_smul_left, hunit]
  ring

lemma turningAffine_hasDerivAt (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) :
    HasDerivAt (turningAffine L v₀ V T Q)
      (((metric (Q L) (V L) (T L) + (V L).1 / v₀) -
        (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀)) / L) s := by
  convert! (((hasDerivAt_id s).div_const L).mul_const
    ((metric (Q L) (V L) (T L) + (V L).1 / v₀) -
      (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀))).const_add
      (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀) using 1
  ring

lemma gauge_hasDerivAt {P A : TMat} {V T : ℝ → Vec} {h : ℝ → ℝ}
    {D : Vec} {h' s : ℝ} (hV : HasDerivAt V D s)
    (hT : HasDerivAt T (-gamma P A (T s) (T s)) s) (hh : HasDerivAt h h' s) :
    HasDerivAt (fun r => V r + h r • T r)
      (D + h' • T s - h s • gamma P A (T s) (T s)) s := by
  apply (hV.add (hh.smul hT)).congr_deriv
  module

lemma normalDensity_deriv_gauge {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    {V T : ℝ → Vec} {h : ℝ → ℝ} {D : Vec} {h' s : ℝ}
    (hunit : metric Q (T s) (T s) = 1) (hV : HasDerivAt V D s)
    (hT : HasDerivAt T (-gamma P A (T s) (T s)) s) (hh : HasDerivAt h h' s) :
    normalDensity P Q A B (T s) (V s + h s • T s)
      (deriv (fun r => V r + h r • T r) s) = normalDensity P Q A B (T s) (V s) D := by
  rw [(gauge_hasDerivAt hV hT hh).deriv]
  exact normalDensity_gauge hQP hQ hP hA hB (T s) (V s) D hunit (h s) h'

lemma turning_boundary_reduction {κ v : ℝ} (hκ : 0 ≤ κ) (hv : 0 ≤ v) (z₀ zL : TVec) :
    κ * v / 4 * ((zL - z₀) 0) ^ 2 ≤ κ * v / 2 * ((z₀ 0) ^ 2 + (zL 0) ^ 2) := by
  have hh := mul_nonneg (mul_nonneg hκ hv) (sq_nonneg (zL 0 + z₀ 0))
  change κ * v / 4 * (zL 0 - z₀ 0) ^ 2 ≤ _
  nlinarith

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

lemma momentumVelocity_unit {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hdet : (coordinateCometric right δ (t s)).det ≠ 0)
    (he : potential right δ p (t s) + v s ^ 2 = 1) :
    metric (metricInverse right δ (t s)) (momentumVelocity right δ p t v s)
      (momentumVelocity right δ p t v s) = 1 := by
  have hQP : metricInverse right δ (t s) * coordinateCometric right δ (t s) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  simp only [momentumVelocity, metric, pairing_inverse hQP]
  rw [dotProduct_comm]
  dsimp only [potential, pairing] at he
  nlinarith

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem returning_normal_nonnegative {right : Bool} {δ C L m : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hwc : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0)
    (hlin : ∀ s ∈ Icc 0 L, HasDerivAt
      (fun r => metric (metricInverse right δ (t r)) (w r, z r)
        (momentumVelocity right δ p t v r)) m s) :
    0 ≤ (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v
      (fun r => (w r, z r)) (fun r => (w' r, z' r)) s) := by
  obtain ⟨hv0, _, hT, hmaps, hsym, _⟩ :=
    returning_dynamics hL hconc ht hv h0 h1 hrange henergy
  have hdet (s : ℝ) (hs : s ∈ Icc 0 L) :
      (coordinateCometric right δ (t s)).det ≠ 0 :=
    (coordinateCometric_posDef (fun q => (hbound (t s)
      ⟨(hmaps hs).1, (hmaps hs).2.trans hT.2.le⟩ q).1)).det_pos.ne'
  have hvL : v L = -v 0 := by simpa only [sub_zero] using (hsym 0 ⟨le_rfl, hL.le⟩).2
  rw [returning_normal_identity hL hdet ht hv h0 h1 hvL hzc hwc hz hw hwa hwb hlin]
  have hh := actual_returning_energy_bound hC hδ hbound hder hconc hdom hL hstar
    ht hv h0 h1 hrange henergy hzc hwc hz hw hwa hwb
  have hb := turning_boundary_reduction (mul_nonneg hδ.1.le (a_nonneg 0)) hv0.le (z 0) (z L)
  have he : e ⬝ᵥ (z L - z 0) = (z L - z 0) 0 := by
    simp [e, dotProduct, Fin.sum_univ_two]
  rw [a_zero] at hb
  rw [he] at hh
  dsimp only [aZero] at hh
  rw [a_zero]
  linarith

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma contDiffAt_pairing {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → TMat} {u v : X → TVec} {x : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hu : ContDiffAt ℝ n u x) (hv : ContDiffAt ℝ n v x) :
    ContDiffAt ℝ n (fun s => pairing (A s) (u s) (v s)) x := by
  unfold pairing Matrix.mulVec dotProduct
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_pi.mp hu i).mul (ContDiffAt.sum fun j _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j).mul (contDiffAt_pi.mp hv j)))

lemma contDiffAt_metric {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Q : X → TMat} {V T : X → Vec} {x : X} {n : WithTop ℕ∞}
    (hQ : ContDiffAt ℝ n Q x) (hV : ContDiffAt ℝ n V x) (hT : ContDiffAt ℝ n T x) :
    ContDiffAt ℝ n (fun s => metric (Q s) (V s) (T s)) x :=
  (hV.fst.mul hT.fst).add (contDiffAt_pairing hQ hV.snd hT.snd)

lemma turningChange_smoothAt {L v₀ s : ℝ} {V T : ℝ → Vec} {Q : ℝ → TMat}
    (hQ : ContDiffAt ℝ ∞ Q s) (hV : ContDiffAt ℝ ∞ V s) (hT : ContDiffAt ℝ ∞ T s) :
    ContDiffAt ℝ ∞ (turningChange L v₀ V T Q) s :=
  ((contDiffAt_const.add ((contDiffAt_id.div_const L).mul contDiffAt_const))).sub
    (contDiffAt_metric hQ hV hT)

lemma turningField_smoothAt {L v₀ s : ℝ} {V T : ℝ → Vec} {Q : ℝ → TMat}
    (hQ : ContDiffAt ℝ ∞ Q s) (hV : ContDiffAt ℝ ∞ V s) (hT : ContDiffAt ℝ ∞ T s) :
    ContDiffAt ℝ ∞ (turningField L v₀ V T Q) s :=
  hV.add ((turningChange_smoothAt hQ hV hT).smul hT)

lemma turningField_tangential_derivative {L v₀ s : ℝ} (hL : 0 < L) (hs : s ∈ Icc 0 L)
    {V T : ℝ → Vec} {Q : ℝ → TMat}
    (hQ : ContDiffAt ℝ ∞ Q s) (hV : ContDiffAt ℝ ∞ V s) (hT : ContDiffAt ℝ ∞ T s)
    (hu : ∀ r ∈ Icc 0 L, metric (Q r) (T r) (T r) = 1) :
    HasDerivAt (fun r => metric (Q r) (turningField L v₀ V T Q r) (T r))
      (((metric (Q L) (V L) (T L) + (V L).1 / v₀) -
        (metric (Q 0) (V 0) (T 0) - (V 0).1 / v₀)) / L) s := by
  have hh := (contDiffAt_metric hQ (turningField_smoothAt (L := L) (v₀ := v₀) hQ hV hT) hT).differentiableAt (by simp)
  have he : ∀ r ∈ Icc 0 L, metric (Q r) (turningField L v₀ V T Q r) (T r) =
      turningAffine L v₀ V T Q r := fun r hr => turningField_tangential V T Q (hu r hr)
  have hw := (turningAffine_hasDerivAt L v₀ V T Q s).hasDerivWithinAt.congr he (he s hs)
  apply hh.hasDerivAt.congr_deriv
  exact ((hh.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc hL s hs)).symm.trans
    (hw.derivWithin (uniqueDiffOn_Icc hL s hs))

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma momentumVelocity_smoothAt {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (ht : ContDiffAt ℝ ∞ t s) (hv : ContDiffAt ℝ ∞ v s) :
    ContDiffAt ℝ ∞ (momentumVelocity right δ p t v) s := by
  apply hv.prodMk
  have hR := (coordinateCometric_smooth right δ).contDiffAt.comp s ht
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ ∞ (fun r => ∑ j : Fin 2, coordinateCometric right δ (t r) i j * p j) s
  exact ContDiffAt.sum (fun j _ => ((contDiffAt_pi.mp (contDiffAt_pi.mp hR i) j).mul contDiffAt_const))

theorem returning_arbitrary_field_nonnegative {right : Bool} {δ C L : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (hta : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {V : ℝ → Vec} (hV : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ V s) :
    0 ≤ (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v V (deriv V) s) := by
  obtain ⟨hv0, _, hT, hmaps, hsym, _⟩ :=
    returning_dynamics hL hconc ht hv h0 h1 hrange henergy
  have hdet (s : ℝ) (hs : s ∈ Icc 0 L) :
      (coordinateCometric right δ (t s)).det ≠ 0 :=
    (coordinateCometric_posDef (fun q => (hbound (t s)
      ⟨(hmaps hs).1, (hmaps hs).2.trans hT.2.le⟩ q).1)).det_pos.ne'
  let T := momentumVelocity right δ p t v
  let Q := fun s => metricInverse right δ (t s)
  let W := turningField L (v 0) V T Q
  have hTa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ T s :=
    momentumVelocity_smoothAt (hta s hs) (hva s hs)
  have hQa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ Q s :=
    (metricInverse_smoothAt (hdet s hs)).comp s (hta s hs)
  have hWa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ W s :=
    turningField_smoothAt (hQa s hs) (hV s hs) (hTa s hs)
  have hWd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt W (deriv W s) s :=
    ((hWa s hs).differentiableAt (by simp)).hasDerivAt
  have hWdc : ContinuousOn (deriv W) (Icc 0 L) := fun s hs =>
    ((hWa s hs).derivWithin (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hu (s : ℝ) (hs : s ∈ Icc 0 L) : metric (Q s) (T s) (T s) = 1 :=
    momentumVelocity_unit (hdet s hs) (henergy s hs)
  have hvL : v L = -v 0 := by simpa only [sub_zero] using (hsym 0 ⟨le_rfl, hL.le⟩).2
  have hW0 : (W 0).1 = 0 := turningField_zero hv0.ne' V T Q rfl
  have hWL : (W L).1 = 0 := turningField_end hL.ne' hv0.ne' V T Q hvL
  have hb := returning_normal_nonnegative hC hδ hbound hder hconc hdom hL hstar
    ht hv h0 h1 hrange henergy hWdc.snd hWdc.fst
    (fun s hs => (hWd s hs).snd) (fun s hs => (hWd s hs).fst) hW0 hWL
    (fun s hs => turningField_tangential_derivative hL hs (hQa s hs) (hV s hs) (hTa s hs) hu)
  have he (s : ℝ) (hs : s ∈ Icc 0 L) :
      returnNormalDensity right δ p t v W (deriv W) s =
      returnNormalDensity right δ p t v V (deriv V) s := by
    apply normalDensity_deriv_gauge
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s hs)))
      (metricInverse_transpose right δ (t s)) (coordinateCometric_transpose right δ (t s))
      (metricInverse_deriv_transpose right δ (t s)) (metricInverse_second_transpose right δ (t s))
      (hu s hs) (((hV s hs).differentiableAt (by simp)).hasDerivAt)
      (momentumVelocity_hasDerivAt (hdet s hs) (ht s hs) (hv s hs))
      (((turningChange_smoothAt (L := L) (v₀ := v 0) (hQa s hs) (hV s hs) (hTa s hs)).differentiableAt (by simp)).hasDerivAt)
  have hei : (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v W (deriv W) s) =
      (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v V (deriv V) s) := by
    apply intervalIntegral.integral_congr
    simpa only [uIcc_of_le hL.le, EqOn] using he
  rw [← hei]
  exact hb

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
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningPassage.returning_arbitrary_field_nonnegative := @_root_.OAI.ThreeManifold.ReturningPassage.returning_arbitrary_field_nonnegative
