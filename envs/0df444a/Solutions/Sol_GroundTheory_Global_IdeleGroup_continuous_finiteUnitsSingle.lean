-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:53.022135+00:00
-- url     : https://prove2.me/submissions/d1d99218-01bb-43d2-97d2-158870fd54a6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteAdeleSingle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteUnitsSingle (K := K) v) :=
  Units.continuous_map (continuous_finiteAdeleSingle v)
end GroundTheory.Global.IdeleGroup
