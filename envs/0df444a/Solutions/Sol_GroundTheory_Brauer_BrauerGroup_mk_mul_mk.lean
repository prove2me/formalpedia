-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.mk_mul_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:14.404045+00:00
-- url     : https://prove2.me/submissions/9151aaa2-ee31-4771-b943-e4fce947fa67

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable (K : Type u) [Field K]
variable {K}
namespace GroundTheory.Brauer
namespace BrauerGroup
theorem _root_.solution (A B : CSA.{u, u} K) :
    (⟦A⟧ * ⟦B⟧ : BrauerGroup.{u, u} K) = ⟦tensorCSA A B⟧ := rfl
end BrauerGroup
end GroundTheory.Brauer
