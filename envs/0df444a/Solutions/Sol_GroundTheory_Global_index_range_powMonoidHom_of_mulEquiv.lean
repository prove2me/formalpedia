-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:44:06.287134+00:00
-- url     : https://prove2.me/submissions/ff25fe77-b5b9-4aa8-9404-1e49e00d7109

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Theorems.Thm_GroundTheory_Global_map_range_powMonoidHom

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
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← map_range_powMonoidHom e n, Subgroup.index_map_equiv]
end GroundTheory.Global
