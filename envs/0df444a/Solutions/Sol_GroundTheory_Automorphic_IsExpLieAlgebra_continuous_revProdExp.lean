-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.continuous_revProdExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:19.514024+00:00
-- url     : https://prove2.me/submissions/fdb37ab9-e072-49a8-b129-12c05d3395a7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_zero
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution : ∀ {d : ℕ} (X : Fin d → 𝔤), Continuous (h.revProdExp X)
  | 0, X => by
    have : h.revProdExp X = fun _ => 1 := funext (h.revProdExp_zero X)
    rw [this]; exact continuous_const
  | d + 1, X => by
    have : h.revProdExp X =
        fun t => h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) :=
      funext (h.revProdExp_succ X)
    rw [this]
    exact ((solution (Fin.tail X)).comp
      (continuous_pi fun j => continuous_apply j.succ)).mul
      (h.continuous_expG.comp ((continuous_apply 0).smul continuous_const))
end GroundTheory.Automorphic.IsExpLieAlgebra
