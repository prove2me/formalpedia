-- Prove2me | solution 1 for GroundTheory.Global.measurePreserving_prodEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:36.928421+00:00
-- url     : https://prove2.me/submissions/fb6171e5-e0e9-4a9f-bdb0-43beec9ea24a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure

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
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution :
    MeasurePreserving (IdeleGroup.prodEquiv K) (ideleMeasure K)
      ((infiniteIdeleMeasure K).prod (finiteIdeleMeasure K)) := by
  have h1 : Measurable (IdeleGroup.prodEquiv K) := (map_continuous _).measurable
  have h2 : Measurable (IdeleGroup.prodEquiv K).symm := (map_continuous _).measurable
  refine ⟨h1, ?_⟩
  rw [ideleMeasure, Measure.map_map h1 h2]
  convert Measure.map_id
  funext x
  exact (IdeleGroup.prodEquiv K).apply_symm_apply x
end GroundTheory.Global
