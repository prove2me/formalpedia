-- Prove2me | solution 1 for GroundTheory.LocalField.isUnramified_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:05.895585+00:00
-- url     : https://prove2.me/submissions/4ba61d95-5cb2-4e91-84fe-e8b6aa01e3b4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs

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
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution : IsUnramified K L ↔ ramificationIndex K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩
end GroundTheory.LocalField
