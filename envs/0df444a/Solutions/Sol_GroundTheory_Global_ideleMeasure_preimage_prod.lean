-- Prove2me | solution 1 for GroundTheory.Global.ideleMeasure_preimage_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:23.483637+00:00
-- url     : https://prove2.me/submissions/22a29622-0932-45e7-8527-df133584cc1a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Theorems.Thm_GroundTheory_Global_measurePreserving_prodEquiv

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
theorem _root_.solution {A : Set (InfiniteAdeleRing K)ˣ}
    {B : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ideleMeasure K (IdeleGroup.prodEquiv K ⁻¹' (A ×ˢ B)) =
      infiniteIdeleMeasure K A * finiteIdeleMeasure K B := by
  rw [(measurePreserving_prodEquiv K).measure_preimage (hA.prod hB).nullMeasurableSet,
    Measure.prod_prod]
end GroundTheory.Global
