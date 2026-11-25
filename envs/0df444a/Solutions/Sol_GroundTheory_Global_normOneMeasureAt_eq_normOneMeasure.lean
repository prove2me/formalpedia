-- Prove2me | solution 1 for GroundTheory.Global.normOneMeasureAt_eq_normOneMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:00.183226+00:00
-- url     : https://prove2.me/submissions/66a57ed6-5504-410f-83fc-9601d5f647fa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Theorems.Thm_GroundTheory_Global_normOneMeasureAt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution (w : InfinitePlace K) :
    normOneMeasureAt w = normOneMeasure K :=
  normOneMeasureAt_eq _ w
end GroundTheory.Global
