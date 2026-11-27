-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramified.iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:38.095358+00:00
-- url     : https://prove2.me/submissions/d91c3b58-111f-47af-84c8-379ea3a2b99e

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
theorem _root_.solution {ι : Type*} (E : ι → IntermediateField K L)
    [∀ i, IsUnramified K (E i)] : IsUnramified K (⨆ i, E i : IntermediateField K L) :=
  IsUnramified.of_le (iSup_le fun i ↦ le_maximalUnramified K L (E i))
end IsUnramified
end GroundTheory.LocalField
