-- Prove2me | solution 1 for GroundTheory.Global.map_restrict_eq_normOneClassMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:52:41.29881+00:00
-- url     : https://prove2.me/submissions/295a2cf5-3539-4ddd-97d6-22656b9b2ae1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {F : Set (normOneSubgroup K)}
    (hF : IsFundamentalDomain (diagonalNormOne K).op F (normOneMeasure K)) :
    Measure.map QuotientGroup.mk ((normOneMeasure K).restrict F) = normOneClassMeasure K :=
  hF.quotientMeasure_eq _ (isFundamentalDomain_normOneFundamentalDomain K _)
end GroundTheory.Global
