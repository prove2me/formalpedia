-- Prove2me | solution 1 for GroundTheory.Global.map_normOneSplitting_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:03:18.303571+00:00
-- url     : https://prove2.me/submissions/168967ef-fbb9-4793-bb52-5bf21496af02

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Theorems.Thm_GroundTheory_Global_map_normOneSplitting_eq_prod_at
import Theorems.Thm_GroundTheory_Global_normOneMeasureAt_eq_normOneMeasure

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
    (ideleMeasure K).map (normOneSplitting w) = (normOneMeasure K).prod posRealMeasure := by
  rw [← normOneMeasureAt_eq_normOneMeasure w, map_normOneSplitting_eq_prod_at]
end GroundTheory.Global
