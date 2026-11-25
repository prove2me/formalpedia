-- Prove2me | solution 1 for GroundTheory.Global.natCard_rootsOfUnity_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:18.366309+00:00
-- url     : https://prove2.me/submissions/a69bb51a-60cb-415a-a7e9-bf83659df8f0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_map_unitsIncl_ker_powMonoidHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {n : ℕ}
namespace GroundTheory.Global
theorem _root_.solution (hn : n ≠ 0) :
    Nat.card (rootsOfUnity n K) = Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker := by
  rw [← map_unitsIncl_ker_powMonoidHom hn, Subgroup.card_map_of_injective unitsIncl_injective]
end GroundTheory.Global
