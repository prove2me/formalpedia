-- Prove2me | solution 1 for GroundTheory.ProfCoh.toAdditive_subtype_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:39.201639+00:00
-- url     : https://prove2.me/submissions/1698af33-671b-43be-b111-cc3a82685cc8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
namespace GroundTheory.ProfCoh
theorem _root_.solution {G : Type*} [CommGroup G] (H : Subgroup G) :
    Function.Injective H.subtype.toAdditive :=
  fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))
end GroundTheory.ProfCoh
