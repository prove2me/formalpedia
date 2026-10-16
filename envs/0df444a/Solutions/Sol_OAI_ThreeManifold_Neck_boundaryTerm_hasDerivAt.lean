-- Prove2me | solution 1 for OAI.ThreeManifold.Neck.boundaryTerm_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:18:28.948005+00:00
-- url     : https://prove2.me/submissions/99320d6c-0050-4af2-b8ba-e53a325d67be

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L299-L318
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Neck.boundaryTerm_hasDerivAt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt

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

lemma pairing_smul_left (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A (r • u) v = r * pairing A u v := by
  simp only [pairing, smul_dotProduct, smul_eq_mul]
lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

lemma sandwich_transpose {P A : TMat} (hP : Pᵀ = P) (hA : Aᵀ = A) :
    (A * P * A)ᵀ = A * P * A := by
  simp only [Matrix.transpose_mul, hA, hP, Matrix.mul_assoc]

lemma pairing_sandwich (P A : TMat) (u v : TVec) :
    pairing A u (P *ᵥ (A *ᵥ v)) = pairing (A * P * A) u v := by
  simp only [pairing, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma pairing_sandwich_left {P A : TMat} (hP : Pᵀ = P) (hA : Aᵀ = A) (u v : TVec) :
    pairing A (P *ᵥ (A *ᵥ u)) v = pairing (A * P * A) u v := by
  rw [pairing_symm hA, pairing_sandwich, pairing_symm (sandwich_transpose hP hA)]

lemma pairing_matrix_smul (A : TMat) (r : ℝ) (u v : TVec) :
    pairing (r • A) u v = r * pairing A u v := by
  simp only [pairing, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma boundaryTerm_hasDerivAt {A : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {P B : TMat} {w' : ℝ} {z' : TVec} {s : ℝ}
    (hP : Pᵀ = P) (hAs : (A (t s))ᵀ = A (t s)) (hB : Bᵀ = B)
    (hA : HasDerivAt A B (t s)) (ht : HasDerivAt t (v s) s)
    (hv : HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu : HasDerivAt u (-v s • (P *ᵥ (A (t s) *ᵥ u s))) s)
    (hw : HasDerivAt w w' s) (hz : HasDerivAt z z' s) :
    HasDerivAt (fun r => boundaryTerm (A (t r)) (v r, u r) (w r, z r))
      (boundaryJet P (A (t s)) B (v s, u s) (w s, z s) (w', z')) s := by
  have hAc := hA.scomp s ht
  have hzz := pairing_hasDerivAt hAc hz hz
  have huz := pairing_hasDerivAt hAc hu hz
  have h := ((hv.const_mul (-(1 / 2 : ℝ))).mul hzz).add (hw.mul huz)
  convert! h using 1
  simp only [boundaryJet, Function.comp_apply, pairing_matrix_smul,
      pairing_smul_left, pairing_sandwich_left hP hAs,
      pairing_symm hAs (z s) z', pairing_symm hAs (u s) (z s),
      pairing_symm hAs (u s) z', pairing_symm hB (u s) (z s),
      pairing_symm (sandwich_transpose hP hAs) (u s) (z s)]
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


theorem solution : type_of% @_root_.OAI.ThreeManifold.Neck.boundaryTerm_hasDerivAt := @_root_.OAI.ThreeManifold.Neck.boundaryTerm_hasDerivAt
