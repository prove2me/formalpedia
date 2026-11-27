-- Prove2me | solution 1 for GroundTheory.Global.RationalIdeles.realEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:30.421107+00:00
-- url     : https://prove2.me/submissions/cbeec91d-ab95-436f-a555-be4a7e6cd3ec

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational

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
attribute [local instance] GroundTheory.Global._p2m_local_instance_d54fe1196b_11
open GroundTheory.Global.RationalIdeles
open IdeleGroup
namespace GroundTheory.Global.RationalIdeles
theorem _root_.solution (x : InfiniteAdeleRing ℚ) :
    realEquiv x = InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (isReal_infinitePlace default) (x default) :=
  rfl
end GroundTheory.Global.RationalIdeles
