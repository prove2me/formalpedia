-- Prove2me | solution 1 for GroundTheory.Global.ideleClassNorm_ideleClassNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:21.352335+00:00
-- url     : https://prove2.me/submissions/40828964-90b2-4730-a01b-30ece43699ef

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap
import Theorems.Thm_GroundTheory_Global_ideleNorm_ideleNorm
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_ideleClassNorm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.ideleClassNorm_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open AdeleBaseChange
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
namespace GroundTheory.Global
theorem _root_.solution (c : IdeleClassGroup M) :
    ideleClassNorm K L (ideleClassNorm L M c) = ideleClassNorm K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective M c
  rw [ideleClassNorm_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleNorm]
end GroundTheory.Global
