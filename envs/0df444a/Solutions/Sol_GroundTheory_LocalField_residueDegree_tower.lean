-- Prove2me | solution 1 for GroundTheory.LocalField.residueDegree_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:24.86227+00:00
-- url     : https://prove2.me/submissions/677c21eb-f482-4258-91a3-13cc3efaa3c0

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
variable [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
namespace GroundTheory.LocalField
theorem _root_.solution :
    residueDegree K M = residueDegree K L * residueDegree L M :=
  Ideal.inertiaDeg_tower _ _
end GroundTheory.LocalField
