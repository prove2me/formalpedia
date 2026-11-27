-- Prove2me | solution 1 for GroundTheory.Automorphic.lieGroup_GL_complex_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:30.378432+00:00
-- url     : https://prove2.me/submissions/2a4175f5-974d-41aa-903c-f6fc573fd979

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie

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
theorem _root_.solution (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) k (GL (Fin n) ℂ) := inferInstance
end GroundTheory.Automorphic
