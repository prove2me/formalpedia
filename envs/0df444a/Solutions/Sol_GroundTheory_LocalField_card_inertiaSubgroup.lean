-- Prove2me | solution 1 for GroundTheory.LocalField.card_inertiaSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:39.6746+00:00
-- url     : https://prove2.me/submissions/1749f0f8-c8f7-47fb-8455-33a4b60953a2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_inertiaSubgroup_counting

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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution : Nat.card (inertiaSubgroup K L) = ramificationIndex K L :=
  (inertiaSubgroup_counting K L).1
end GroundTheory.LocalField
