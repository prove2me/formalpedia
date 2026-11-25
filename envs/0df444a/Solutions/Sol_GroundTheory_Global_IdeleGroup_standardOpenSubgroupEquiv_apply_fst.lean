-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:36.096354+00:00
-- url     : https://prove2.me/submissions/c95d31a1-e56f-42cd-a73b-45dad4f3ac86

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : standardOpenSubgroup K) :
    (standardOpenSubgroupEquiv K x).1 = toInfinite K (x : IdeleGroup K) :=
  rfl
end GroundTheory.Global.IdeleGroup
