-- Prove2me | solution 1 for GroundTheory.LocalField.card_lowerRamificationGroup_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:28.278787+00:00
-- url     : https://prove2.me/submissions/5f91ded8-a5be-4904-ba3f-ff48b36b0f8d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Theorems.Thm_GroundTheory_LocalField_card_inertiaSubgroup
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_zero


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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution [IsGalois K L] :
    Nat.card (lowerRamificationGroup K L 0) = ramificationIndex K L := by
  rw [lowerRamificationGroup_zero]
  exact card_inertiaSubgroup K L
end GroundTheory.LocalField
