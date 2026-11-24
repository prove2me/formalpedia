-- Prove2me | solution 1 for GlobalTheory.T.finsum_fiberwise_of_finite_support_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:29.719196+00:00
-- url     : https://prove2.me/submissions/45043c33-bbc8-4f91-a78f-1b8d367d6a29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumFiberwiseOfFiniteSupportComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumFiberwiseOfFiniteSupportComplexStatement
import Theorems.Thm_GlobalTheory_finsum_fiberwise_of_finite_support


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} (ρ : A → B) (f : A → ℂ), (Function.support f).Finite → ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  first | exact @GlobalTheory.finsum_fiberwise_of_finite_support | exact GlobalTheory.finsum_fiberwise_of_finite_support | (intros; apply GlobalTheory.finsum_fiberwise_of_finite_support <;> assumption)
end _root_.GlobalTheory.T
