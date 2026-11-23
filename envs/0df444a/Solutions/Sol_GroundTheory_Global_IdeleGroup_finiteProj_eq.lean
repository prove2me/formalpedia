-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:41.468076+00:00
-- url     : https://prove2.me/submissions/7e888e07-8dbe-4c39-b8c8-fd7909ed9a55

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
open GroundTheory GroundTheory.Global
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteProj v x = (prodRestrictedEquiv K x).2 v :=
  Units.ext rfl
end GroundTheory.Global.IdeleGroup
