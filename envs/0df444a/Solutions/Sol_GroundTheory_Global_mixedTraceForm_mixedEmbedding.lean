-- Prove2me | solution 1 for GroundTheory.Global.mixedTraceForm_mixedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:44.458038+00:00
-- url     : https://prove2.me/submissions/35e74a0c-2011-4297-b6c3-9c3813bff4e9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Theorems.Thm_GroundTheory_Global_mixedTrace_mixedEmbedding
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_apply

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
theorem _root_.solution (a b : K) :
    mixedTraceForm K (mixedEmbedding K a) (mixedEmbedding K b) = (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [mixedTraceForm_apply, ← map_mul, mixedTrace_mixedEmbedding]
end GroundTheory.Global
