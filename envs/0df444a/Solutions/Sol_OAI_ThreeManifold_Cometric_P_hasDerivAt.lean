-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.P_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:27:43.325445+00:00
-- url     : https://prove2.me/submissions/51706c1c-1006-4307-9d61-d07677aa71ff

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L918-L932
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.P_hasDerivAt. The node keeps its source
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

lemma d₁_hasDerivAt (δ t : ℝ) : HasDerivAt (d₁ δ) (u₁ δ t) t := by
  convert! (hasDerivAt_const t (1 : ℝ)).add ((A_hasDerivAt t).const_mul δ) using 1
  simp [u₁]

lemma d₂_hasDerivAt (δ t : ℝ) : HasDerivAt (d₂ δ) (u₂ δ t) t := by
  have h := (A_hasDerivAt (1 - t)).comp t ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert! (hasDerivAt_const t (1 : ℝ)).add (h.const_mul δ) using 1
  simp [u₂]

lemma shear_hasDerivAt (δ t : ℝ) : HasDerivAt (shear δ) (v δ t) t :=
  ((χ_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

lemma P_hasDerivAt (δ t : ℝ) : HasDerivAt (P δ) (P₁ δ t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h1 := d₁_hasDerivAt δ t
  have h2 := d₂_hasDerivAt δ t
  have hs := shear_hasDerivAt δ t
  fin_cases i <;> fin_cases j <;> dsimp [P, P₁]
  · convert! h1.add (h2.mul (hs.pow 2)) using 1
    dsimp only [Pi.pow_apply]
    ring
  · exact (h2.mul hs)
  · exact (h2.mul hs)
  · exact h2

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.P_hasDerivAt := @_root_.OAI.ThreeManifold.Cometric.P_hasDerivAt
