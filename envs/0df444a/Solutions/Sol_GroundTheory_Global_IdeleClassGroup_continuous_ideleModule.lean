-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.continuous_ideleModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:14.148033+00:00
-- url     : https://prove2.me/submissions/ab5ab31a-fb12-419b-a3c9-4703b8c8ded2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_ideleModule

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
theorem _root_.solution : Continuous (ideleModule K) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (IdeleGroup.continuous_ideleModule (K := K))
end GroundTheory.Global.IdeleClassGroup
