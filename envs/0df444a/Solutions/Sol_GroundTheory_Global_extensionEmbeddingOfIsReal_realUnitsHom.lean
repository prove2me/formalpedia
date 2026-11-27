-- Prove2me | solution 1 for GroundTheory.Global.extensionEmbeddingOfIsReal_realUnitsHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:27.567382+00:00
-- url     : https://prove2.me/submissions/1f56da13-e15f-4d02-ab82-defa29ab65a8

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
theorem _root_.solution {w : InfinitePlace K} (hw : w.IsReal) (x : ℝˣ) :
    extensionEmbeddingOfIsReal hw ((realUnitsHom hw x : (w.Completion)ˣ) : w.Completion) = x := by
  rw [← ringEquivRealOfIsReal_apply]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _
end GroundTheory.Global
