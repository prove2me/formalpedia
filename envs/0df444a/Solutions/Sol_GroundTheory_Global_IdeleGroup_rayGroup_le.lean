-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.rayGroup_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:18.715977+00:00
-- url     : https://prove2.me/submissions/a65fff82-7ce5-4085-a601-84badde49f1c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Theorems.Thm_GroundTheory_Global_IdeleGroup_map_idealLevel_le_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_map_infinitePositive_le_standardOpenSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (𝔪 : Ideal (𝓞 K)) :
    rayGroup K 𝔪 ≤ (diagonal K).range ⊔ standardOpenSubgroup K :=
  sup_le (sup_le le_sup_left ((map_idealLevel_le_standardOpenSubgroup 𝔪).trans le_sup_right))
    (map_infinitePositive_le_standardOpenSubgroup.trans le_sup_right)
end GroundTheory.Global.IdeleGroup
