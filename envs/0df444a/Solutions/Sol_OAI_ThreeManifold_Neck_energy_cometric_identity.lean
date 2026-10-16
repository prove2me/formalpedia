-- Prove2me | solution 1 for OAI.ThreeManifold.Neck.energy_cometric_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:21:41.251947+00:00
-- url     : https://prove2.me/submissions/dc1d1ffe-dfdc-4801-87ce-980591bcb6db

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L440-L463
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Neck.energy_cometric_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

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

lemma pairing_matrix_smul (A : TMat) (r : ℝ) (u v : TVec) :
    pairing (r • A) u v = r * pairing A u v := by
  simp only [pairing, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma pairing_matrix_neg (A : TMat) (u v : TVec) :
    pairing (-A) u v = -pairing A u v := by
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

lemma pairing_mulVec_left (A L : TMat) (u v : TVec) :
    pairing A (L *ᵥ u) v = pairing (Lᵀ * A) u v := by
  unfold pairing
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

lemma pairing_mulVec_right (A L : TMat) (u v : TVec) :
    pairing A u (L *ᵥ v) = pairing (A * L) u v := by
  simp only [pairing, Matrix.mulVec_mulVec]

lemma energy_cometric_identity {P Q H K : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hH : Hᵀ = H)
    (p : TVec) (v : ℝ) (V Vdot : Vec) :
    coordinateEnergyDensity Q (-Q * H * Q)
      ((2 : ℝ) • (Q * H * Q * H * Q) - Q * K * Q) (v, P *ᵥ p) V Vdot =
    Vdot.1 ^ 2 + pairing Q (Vdot.2 - V.1 • (H *ᵥ p))
      (Vdot.2 - V.1 • (H *ᵥ p)) - (1 / 2 : ℝ) * pairing K p p * V.1 ^ 2 := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hfirst : (-Q * H * Q) * P = -(Q * H) := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_one, neg_mul]
  have hsecond : P * ((2 : ℝ) • (Q * H * Q * H * Q) - Q * K * Q) * P =
      (2 : ℝ) • (H * Q * H) - K := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
  have hHQH : pairing (H * Q * H) p p = pairing Q (H *ᵥ p) (H *ᵥ p) := by
    rw [pairing_mulVec_left, pairing_mulVec_right, hH]
  simp only [coordinateEnergyDensity, pairing_mulVec_right, pairing_mulVec_left,
    hP, hfirst]
  rw [← Matrix.mul_assoc, hsecond, pairing_matrix_sub, pairing_matrix_smul, hHQH]
  simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
    pairing_matrix_neg]
  rw [← pairing_mulVec_right Q H, pairing_symm hQ (H *ᵥ p) Vdot.2]
  ring

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

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Neck.energy_cometric_identity := @_root_.OAI.ThreeManifold.Neck.energy_cometric_identity
