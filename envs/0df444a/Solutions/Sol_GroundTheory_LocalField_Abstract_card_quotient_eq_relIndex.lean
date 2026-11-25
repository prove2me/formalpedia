-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.card_quotient_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:31.452191+00:00
-- url     : https://prove2.me/submissions/acb51335-abf5-4632-9a39-e1ed5c17ced0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (K L : Subgroup G) :
    Nat.card (K ⧸ L.subgroupOf K) = L.relIndex K :=
  (Subgroup.index_eq_card _).symm
end GroundTheory.LocalField.Abstract
