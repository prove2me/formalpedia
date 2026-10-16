-- Prove2me | solution 1 for OAI.ThreeManifold.Neck.pairing_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:17:08.527346+00:00
-- url     : https://prove2.me/submissions/76b62a0d-babe-4d92-baf2-b40afc5b0b7c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L276-L293
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Neck.pairing_hasDerivAt. The node keeps its source
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

lemma pairing_hasDerivAt {A : ℝ → TMat} {u v : ℝ → TVec}
    {A' : TMat} {u' v' : TVec} {s : ℝ}
    (hA : HasDerivAt A A' s) (hu : HasDerivAt u u' s) (hv : HasDerivAt v v' s) :
    HasDerivAt (fun r => pairing (A r) (u r) (v r))
      (pairing (A s) u' (v s) + pairing A' (u s) (v s) +
        pairing (A s) (u s) v') s := by
  have hAe (i j : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j
  have hue (i : Fin 2) := hasDerivAt_pi.mp hu i
  have hve (i : Fin 2) := hasDerivAt_pi.mp hv i
  have h := ((hue 0).mul (((hAe 0 0).mul (hve 0)).add ((hAe 0 1).mul (hve 1)))).add
    ((hue 1).mul (((hAe 1 0).mul (hve 0)).add ((hAe 1 1).mul (hve 1))))
  convert! h using 1
  · funext r
    simp only [pairing, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Pi.add_apply, Pi.mul_apply]
  · simp only [pairing, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Pi.add_apply, Pi.mul_apply]
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


theorem solution : type_of% @_root_.OAI.ThreeManifold.Neck.pairing_hasDerivAt := @_root_.OAI.ThreeManifold.Neck.pairing_hasDerivAt
