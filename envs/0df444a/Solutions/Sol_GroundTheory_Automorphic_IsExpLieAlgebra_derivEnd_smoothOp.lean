-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.derivEnd_smoothOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:31.066763+00:00
-- url     : https://prove2.me/submissions/817c3025-fa0e-4ac3-852f-e3a573cac6bf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivOp_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (g : G) (X : 𝔤) :
    h.derivEnd π (h.Ad g X) ∘ₗ h.smoothOp π g = h.smoothOp π g ∘ₗ h.derivEnd π X := by
  ext v
  exact h.derivOp_map π v.2 g X
end GroundTheory.Automorphic.IsExpLieAlgebra
