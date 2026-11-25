-- Prove2me | solution 1 for GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:06.231717+00:00
-- url     : https://prove2.me/submissions/33f43e1e-8ed8-4547-a56e-96234952ff43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegralStatement
import Theorems.Thm_GlobalTheory_LocBounded_bounded_of_isIntegral


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by
  first | exact @GlobalTheory.LocBounded.bounded_of_isIntegral | exact GlobalTheory.LocBounded.bounded_of_isIntegral | (intros; apply GlobalTheory.LocBounded.bounded_of_isIntegral <;> assumption)
end _root_.GlobalTheory.T
