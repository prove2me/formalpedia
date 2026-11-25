-- Prove2me | solution 1 for GroundTheory.Global.mixedTraceForm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:31.925355+00:00
-- url     : https://prove2.me/submissions/db7dca86-28c2-47a3-bb86-5776661a3273

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_separatingLeft

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
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution : (mixedTraceForm K).Nondegenerate :=
  ⟨mixedTraceForm_separatingLeft K, fun y hy =>
    mixedTraceForm_separatingLeft K y fun x => by rw [mixedTraceForm_comm]; exact hy x⟩
end GroundTheory.Global
