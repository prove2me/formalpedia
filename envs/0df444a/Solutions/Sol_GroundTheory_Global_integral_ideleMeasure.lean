-- Prove2me | solution 1 for GroundTheory.Global.integral_ideleMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:34.420936+00:00
-- url     : https://prove2.me/submissions/0172b134-2a86-4b72-adec-da720b9b1668

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : IdeleGroup K → E) :
    ∫ x, f x ∂ideleMeasure K = ∫ p, f ((IdeleGroup.prodEquiv K).symm p)
      ∂(infiniteIdeleMeasure K).prod (finiteIdeleMeasure K) := by
  exact integral_map_equiv (IdeleGroup.prodEquiv K).symm.toHomeomorph.toMeasurableEquiv f
end GroundTheory.Global
