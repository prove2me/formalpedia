-- Prove2me | solution 1 for GroundTheory.Global.infiniteAdeleMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:03.206182+00:00
-- url     : https://prove2.me/submissions/cc00c82d-75c0-4f5f-a8bd-b0729bd9cb2c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling

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
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (K)
namespace GroundTheory.Global
theorem _root_.solution (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K E = selfDualMeasure K (homeomorphMixedSpace K '' E) := by
  rw [infiniteAdeleMeasure, MeasurableEquiv.map_apply]
  exact congrArg _ ((measurableEquivMixedSpace K).image_eq_preimage_symm E).symm
end GroundTheory.Global
