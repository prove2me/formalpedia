-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_latticeDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:02.844599+00:00
-- url     : https://prove2.me/submissions/e2d0cdd4-b849-4d23-8857-e227a87b58a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
namespace GroundTheory.Automorphic
theorem _root_.solution {L : AddSubgroup X} {y : X} :
    y ∈ latticeDual L ↔ ∀ x ∈ L, ∃ n : ℤ, ⟪y, x⟫ = n := Iff.rfl
end GroundTheory.Automorphic
