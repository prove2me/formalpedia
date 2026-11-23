-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.ideleModule_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:04.549709+00:00
-- url     : https://prove2.me/submissions/d01e45f6-d367-4e06-82a2-397e35370025

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms

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
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleClassGroup
namespace GroundTheory.Global.IdeleClassGroup
theorem _root_.solution (x : IdeleGroup K) :
    ideleModule K (mk K x) = IdeleGroup.ideleModule K x :=
  rfl
end GroundTheory.Global.IdeleClassGroup
