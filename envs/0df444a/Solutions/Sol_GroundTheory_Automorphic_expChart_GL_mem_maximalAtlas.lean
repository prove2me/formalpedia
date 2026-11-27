-- Prove2me | solution 1 for GroundTheory.Automorphic.expChart_GL_mem_maximalAtlas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:26.763836+00:00
-- url     : https://prove2.me/submissions/79fca98c-8817-448f-a2e5-57c831c91d20

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Theorems.Thm_GroundTheory_Automorphic_expChartUnits_mem_maximalAtlas

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
open NormedSpace Set
set_option linter.unusedSectionVars false
open scoped Matrix.Norms.L2Operator
namespace GroundTheory.Automorphic
theorem _root_.solution (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (g : GL (Fin n) 𝕂)
    (k : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) :=
  expChartUnits_mem_maximalAtlas 𝕂 g k
end GroundTheory.Automorphic
