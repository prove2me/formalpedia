-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.prod_map_infiniteAdeleSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:40.844785+00:00
-- url     : https://prove2.me/submissions/450f4290-4df4-49ca-8fa8-2352ad0df240

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : (InfiniteAdeleRing K)ˣ) :
    ∏ w, Units.map (infiniteAdeleSingle w) (infiniteComponent w x) = x := by
  classical
  apply Units.ext
  rw [Units.coe_prod]
  exact Finset.univ_prod_mulSingle (fun w : InfinitePlace K ↦ (x : InfiniteAdeleRing K) w)
end GroundTheory.Global.IdeleGroup
