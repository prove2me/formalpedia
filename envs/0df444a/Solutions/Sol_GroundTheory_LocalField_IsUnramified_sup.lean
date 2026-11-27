-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramified.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:31.508687+00:00
-- url     : https://prove2.me/submissions/fcb7be28-7f28-494c-b516-76f07f049abb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_le_maximalUnramified
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_of_le

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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
namespace IsUnramified
theorem _root_.solution (E F : IntermediateField K L) [IsUnramified K E] [IsUnramified K F] :
    IsUnramified K (E ⊔ F : IntermediateField K L) :=
  IsUnramified.of_le (sup_le (le_maximalUnramified K L E) (le_maximalUnramified K L F))
end IsUnramified
end GroundTheory.LocalField
