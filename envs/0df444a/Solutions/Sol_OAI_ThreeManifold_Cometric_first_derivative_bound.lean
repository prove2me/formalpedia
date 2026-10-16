-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.first_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:32:10.821589+00:00
-- url     : https://prove2.me/submissions/15c64d0c-18d3-492f-81d6-01e17ab7ea9d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L1190-L1204
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.first_derivative_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Theorems.Thm_OAI_ThreeManifold_Cometric_sqnorm_mulVec_le

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

lemma P₁_split (δ t : ℝ) :
    P₁ δ t = diagonal ![u₁ δ t, u₂ δ t] + δ ^ 2 • N₁ δ t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P₁, N₁, shear, u₁, u₂, v] <;> ring

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

lemma sqnorm_add_le (p q : V2) :
    sqnorm (p + q) ≤ 2 * sqnorm p + 2 * sqnorm q := by
  simp only [sqnorm, Pi.add_apply]
  nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]

lemma sqnorm_smul (r : ℝ) (p : V2) : sqnorm (r • p) = r ^ 2 * sqnorm p := by
  simp only [sqnorm, Pi.smul_apply, smul_eq_mul]
  ring

lemma a_sq_le_one (t : ℝ) : a t ^ 2 ≤ 1 := by
  nlinarith [a_nonneg t, a_lt_one t]

lemma diagonal_first_bound (δ t : ℝ) (p : V2) :
    sqnorm ((diagonal ![u₁ δ t, u₂ δ t]) *ᵥ p) ≤ δ ^ 2 * sqnorm p := by
  have ha := mul_le_mul_of_nonneg_right (a_sq_le_one t)
    (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 0)))
  have hb := mul_le_mul_of_nonneg_right (a_sq_le_one (1 - t))
    (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 1)))
  simp [sqnorm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, u₁, u₂]
  nlinarith

lemma first_derivative_bound {δ t B : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hB : 0 ≤ B)
    (hN : ∀ i j, |N₁ δ t i j| ≤ B) (p : V2) :
    sqnorm (P₁ δ t *ᵥ p) ≤ (2 + 8 * B ^ 2) * δ ^ 2 * sqnorm p := by
  have hd := diagonal_first_bound δ t p
  have hn := sqnorm_mulVec_le hB hN p
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [hδ.1, hδ.2]
  have hδ4 : (δ ^ 2) ^ 2 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
  have hn' := mul_le_mul_of_nonneg_left hn (sq_nonneg (δ ^ 2))
  have he := mul_le_mul_of_nonneg_right hδ4
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg B)) (sqnorm_nonneg p))
  rw [P₁_split, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hs := sqnorm_add_le ((diagonal ![u₁ δ t, u₂ δ t]) *ᵥ p)
    (δ ^ 2 • (N₁ δ t *ᵥ p))
  rw [sqnorm_smul] at hs
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


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.first_derivative_bound := @_root_.OAI.ThreeManifold.Cometric.first_derivative_bound
