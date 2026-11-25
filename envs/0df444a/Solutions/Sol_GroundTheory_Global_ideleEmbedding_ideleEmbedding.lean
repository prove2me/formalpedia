-- Prove2me | solution 1 for GroundTheory.Global.ideleEmbedding_ideleEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:01:56.885601+00:00
-- url     : https://prove2.me/submissions/f2d41a2b-2587-41ce-98ef-6211be3c191b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap

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
open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open AdeleBaseChange
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
namespace GroundTheory.Global
theorem _root_.solution (x : IdeleGroup K) :
    ideleEmbedding L M (ideleEmbedding K L x) = ideleEmbedding K M x :=
  Units.ext (adeleMap_adeleMap (x : 𝔸[K]))
end GroundTheory.Global
