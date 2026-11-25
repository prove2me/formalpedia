-- Prove2me | solution 1 for GroundTheory.Global.normAtPlace_homeomorphMixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:07.911237+00:00
-- url     : https://prove2.me/submissions/da59dc40-8867-4212-9906-86c59e76f0da

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_apply


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
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    normAtPlace w (homeomorphMixedSpace K x) = ‖x w‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, homeomorphMixedSpace_apply,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex hw, homeomorphMixedSpace_apply,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
end GroundTheory.Global
