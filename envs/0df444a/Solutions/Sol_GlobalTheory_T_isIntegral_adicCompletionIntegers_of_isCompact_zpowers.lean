-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:43.546953+00:00
-- url     : https://prove2.me/submissions/7f18976a-1409-42f2-a66a-2feffab303fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowersStatement
import Theorems.Thm_GlobalTheory_isIntegral_of_isCompact_closure_zpowers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))) → IsIntegral (w.adicCompletionIntegers E) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.isIntegral_of_isCompact_closure_zpowers | exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.isIntegral_of_isCompact_closure_zpowers <;> assumption)
end _root_.GlobalTheory.T
