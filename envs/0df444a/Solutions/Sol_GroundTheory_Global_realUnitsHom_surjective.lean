-- Prove2me | solution 1 for GroundTheory.Global.realUnitsHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:21.778105+00:00
-- url     : https://prove2.me/submissions/e9f686ec-08da-4011-9ef5-61933222033b

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
open NumberField.InfinitePlace.Completion
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {w : InfinitePlace K} (hw : w.IsReal) (a : (w.Completion)ˣ) :
    realUnitsHom hw (Units.map (ringEquivRealOfIsReal hw : w.Completion →+* ℝ).toMonoidHom a) = a :=
  Units.ext ((ringEquivRealOfIsReal hw).symm_apply_apply _)
end GroundTheory.Global
