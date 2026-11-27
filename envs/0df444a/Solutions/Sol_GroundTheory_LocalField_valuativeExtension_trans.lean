-- Prove2me | solution 1 for GroundTheory.LocalField.valuativeExtension_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:44.507384+00:00
-- url     : https://prove2.me/submissions/d2c2ef3e-4e61-4af2-a98a-f3975b2aa7aa

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
variable (K L M : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Field M] [ValuativeRel M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
namespace GroundTheory.LocalField
theorem _root_.solution [ValuativeExtension K L] [ValuativeExtension L M] :
    ValuativeExtension K M where
  vle_iff_vle a b := by
    rw [IsScalarTower.algebraMap_apply K L M, IsScalarTower.algebraMap_apply K L M,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]
end GroundTheory.LocalField
