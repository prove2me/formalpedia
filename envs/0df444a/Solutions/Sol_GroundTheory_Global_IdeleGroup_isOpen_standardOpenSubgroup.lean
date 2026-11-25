-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isOpen_standardOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:13.405898+00:00
-- url     : https://prove2.me/submissions/3badbac1-9264-40df-8fd6-13cc16582c6d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_integralAtFinite

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
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : IsOpen (standardOpenSubgroup K : Set (IdeleGroup K)) :=
  Submonoid.isOpen_units (isOpen_integralAtFinite K)
end GroundTheory.Global.IdeleGroup
