-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramified.of_tower_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:33.935858+00:00
-- url     : https://prove2.me/submissions/10d64e86-f05a-45d3-aa28-7742186bdc97

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Theorems.Thm_GroundTheory_LocalField_isUnramified_tower_iff

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
variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]
namespace GroundTheory.LocalField
namespace IsUnramified
theorem _root_.solution [IsUnramified K M] : IsUnramified K L :=
  ((isUnramified_tower_iff K L M).1 inferInstance).1
end IsUnramified
end GroundTheory.LocalField
