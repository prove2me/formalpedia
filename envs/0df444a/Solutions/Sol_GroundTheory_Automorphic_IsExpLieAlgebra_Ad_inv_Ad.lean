-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.Ad_inv_Ad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:34.76248+00:00
-- url     : https://prove2.me/submissions/a18bd548-1a0a-48a2-9581-c4fd28cef584

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_mul
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (g : G) (X : 𝔤) : h.Ad g⁻¹ (h.Ad g X) = X := by
  rw [← LinearMap.comp_apply, ← Ad_mul, inv_mul_cancel, Ad_one, LinearMap.id_apply]
end GroundTheory.Automorphic.IsExpLieAlgebra
