-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.sqnorm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:30:52.247+00:00
-- url     : https://prove2.me/submissions/c3e6a67a-bc3e-40b5-8f80-d2e44762152b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L1128-L1141
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.sqnorm_mulVec_le. The node keeps its source
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

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

lemma sqnorm_nonneg (p : V2) : 0 ≤ sqnorm p := by unfold sqnorm; positivity

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

lemma dotProduct_sq_le (p q : V2) : (p ⬝ᵥ q) ^ 2 ≤ sqnorm p * sqnorm q := by
  simp only [dotProduct, Fin.sum_univ_two, sqnorm]
  nlinarith [sq_nonneg (p 0 * q 1 - p 1 * q 0)]

lemma sq_le_of_abs_le {x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg x) hB).mpr hx
  simpa only [sq_abs] using h

lemma sqnorm_mulVec_le {M : Mat2} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) (p : V2) :
    sqnorm (M *ᵥ p) ≤ 4 * B ^ 2 * sqnorm p := by
  have h0 := dotProduct_sq_le (M 0) p
  have h1 := dotProduct_sq_le (M 1) p
  have h00 := sq_le_of_abs_le hB (hM 0 0)
  have h01 := sq_le_of_abs_le hB (hM 0 1)
  have h10 := sq_le_of_abs_le hB (hM 1 0)
  have h11 := sq_le_of_abs_le hB (hM 1 1)
  have hm0 := mul_le_mul_of_nonneg_right (add_le_add h00 h01) (sqnorm_nonneg p)
  have hm1 := mul_le_mul_of_nonneg_right (add_le_add h10 h11) (sqnorm_nonneg p)
  change (M 0 ⬝ᵥ p) ^ 2 + (M 1 ⬝ᵥ p) ^ 2 ≤ _
  dsimp only [sqnorm] at h0 h1 hm0 hm1 ⊢
  nlinarith

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.sqnorm_mulVec_le := @_root_.OAI.ThreeManifold.Cometric.sqnorm_mulVec_le
