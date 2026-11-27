-- Prove2me | solution 1 for GroundTheory.Automorphic.BanachRep.coe_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:43.400337+00:00
-- url     : https://prove2.me/submissions/2f38695d-d42b-4935-903b-b0288a19278e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors

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
open GroundTheory.Automorphic.BanachRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (π : BanachRep G E)
namespace GroundTheory.Automorphic.BanachRep
theorem _root_.solution (g : G) : π g = π.toHom g := rfl
end GroundTheory.Automorphic.BanachRep
