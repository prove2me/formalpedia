-- Prove2me | solution 1 for GroundTheory.Global.measurePreserving_measurableEquivMixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:03.725798+00:00
-- url     : https://prove2.me/submissions/cf6b7586-159b-48dd-bfc9-964023e5ab3a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure

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
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution :
    MeasurePreserving (measurableEquivMixedSpace K) (infiniteAdeleMeasure K) (selfDualMeasure K) :=
  MeasurePreserving.symm _ (⟨(measurableEquivMixedSpace K).symm.measurable, rfl⟩ :
    MeasurePreserving (measurableEquivMixedSpace K).symm (selfDualMeasure K) (infiniteAdeleMeasure K))
end GroundTheory.Global
