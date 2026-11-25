-- Prove2me | solution 1 for GroundTheory.Global.map_normOneSplitting_eq_prod_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:06:46.618486+00:00
-- url     : https://prove2.me/submissions/77132ca8-36d6-4cf0-a097-341815c98e83

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Theorems.Thm_GroundTheory_Global_eq_prod_map_fst_restrict

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
    (ideleMeasure K).map (normOneSplitting w) = (normOneMeasureAt w).prod posRealMeasure :=
  eq_prod_map_fst_restrict _ posRealMeasure posRealMeasure_posRealUnitInterval
end GroundTheory.Global
