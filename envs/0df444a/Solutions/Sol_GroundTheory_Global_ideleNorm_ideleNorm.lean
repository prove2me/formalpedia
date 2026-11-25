-- Prove2me | solution 1 for GroundTheory.Global.ideleNorm_ideleNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:13.22683+00:00
-- url     : https://prove2.me/submissions/f88f33cd-0fd6-481a-8876-b234340f49c4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_norm

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
theorem _root_.solution (x : IdeleGroup M) :
    ideleNorm K L (ideleNorm L M x) = ideleNorm K M x :=
  Units.ext (norm_adeleRing_norm (K := K) (L := L) (x : 𝔸[M]))
end GroundTheory.Global
