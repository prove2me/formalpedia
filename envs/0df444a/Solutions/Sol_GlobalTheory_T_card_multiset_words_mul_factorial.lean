-- Prove2me | solution 1 for GlobalTheory.T.card_multiset_words_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:19.703527+00:00
-- url     : https://prove2.me/submissions/d83d7c2a-5264-4a06-aa7f-414182fc65bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorialStatement
import Theorems.Thm_GlobalTheory_MultinomialCount_card_mul_prod_factorial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k → (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial = k.factorial := by
  first | exact @GlobalTheory.MultinomialCount.card_mul_prod_factorial | exact GlobalTheory.MultinomialCount.card_mul_prod_factorial | (intros; apply GlobalTheory.MultinomialCount.card_mul_prod_factorial <;> assumption)
end _root_.GlobalTheory.T
