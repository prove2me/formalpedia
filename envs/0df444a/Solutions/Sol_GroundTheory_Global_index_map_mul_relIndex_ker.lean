-- Prove2me | solution 1 for GroundTheory.Global.index_map_mul_relIndex_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:19.965161+00:00
-- url     : https://prove2.me/submissions/01a1b306-1fad-41e8-a323-11ebff05564d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexFormula

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
variable {G C : Type*} [Group G] [Group C]
namespace GroundTheory.Global
theorem _root_.solution {f : G →* C} (hf : Function.Surjective f) (W : Subgroup G)
    [W.Normal] : (W.map f).index * W.relIndex f.ker = W.index := by
  rw [Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one,
    ← Subgroup.relIndex_sup_left, mul_comm, Subgroup.relIndex_mul_index le_sup_left]
end GroundTheory.Global
