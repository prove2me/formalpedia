-- Prove2me | solution 1 for GroundTheory.Global.map_mul_left_infiniteAdeleMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:34:52.082429+00:00
-- url     : https://prove2.me/submissions/353522cd-e0e8-4635-8057-f35dd7dce8fb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Theorems.Thm_GroundTheory_Global_infiniteAdeleMeasure_smul

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
namespace GroundTheory.Global
theorem _root_.solution (b : (InfiniteAdeleRing K)ˣ) :
    (infiniteAdeleMeasure K).map (fun y ↦ (b : InfiniteAdeleRing K) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ •
        infiniteAdeleMeasure K := by
  ext S hS
  rw [map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul,
    ← infiniteAdeleMeasure_smul]
  congr 1
  exact Set.preimage_smul b S
end GroundTheory.Global
