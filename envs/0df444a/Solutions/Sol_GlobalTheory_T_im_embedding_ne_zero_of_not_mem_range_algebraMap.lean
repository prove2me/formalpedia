-- Prove2me | solution 1 for GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:34.696001+00:00
-- url     : https://prove2.me/submissions/d4e873d8-8c07-478d-8481-708d3aff892d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 := by
  first | exact @GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | exact GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | (intros; apply GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic <;> assumption)
end _root_.GlobalTheory.T
