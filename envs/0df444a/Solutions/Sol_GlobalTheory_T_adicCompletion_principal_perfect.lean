-- Prove2me | solution 1 for GlobalTheory.T.adicCompletion_principal_perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:27.277404+00:00
-- url     : https://prove2.me/submissions/157f3310-0574-4a73-b526-72c318c0b8ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfectStatement
import Theorems.Thm_GlobalTheory_PerfectCompletion_perfect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l] [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧ Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  first | exact @GlobalTheory.PerfectCompletion.perfect | exact GlobalTheory.PerfectCompletion.perfect | (intros; apply GlobalTheory.PerfectCompletion.perfect <;> assumption)
end _root_.GlobalTheory.T
