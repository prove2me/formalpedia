-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.baseChange_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:27.631806+00:00
-- url     : https://prove2.me/submissions/3c6b9a7e-f0ea-4c4f-a593-9b4ff7d31feb

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_comp

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
namespace GroundTheory.Brauer.BrauerGroup
theorem _root_.solution (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (x : BrauerGroup.{u, u} K) :
    baseChange L M (baseChange K L x) = baseChange K M x :=
  DFunLike.congr_fun (baseChange_comp K L M) x
end GroundTheory.Brauer.BrauerGroup
