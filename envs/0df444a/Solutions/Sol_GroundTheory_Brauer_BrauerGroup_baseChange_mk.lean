-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.baseChange_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:07.058175+00:00
-- url     : https://prove2.me/submissions/657b87d9-1c66-4b35-9be4-1a2d9678de68

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange

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
universe u v
open GroundTheory.Brauer.BrauerGroup
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
variable {K L}
namespace GroundTheory.Brauer.BrauerGroup
theorem _root_.solution (A : CSA.{u, u} K) :
    baseChange K L ⟦A⟧ = ⟦baseChangeCSA L A⟧ := rfl
end GroundTheory.Brauer.BrauerGroup
