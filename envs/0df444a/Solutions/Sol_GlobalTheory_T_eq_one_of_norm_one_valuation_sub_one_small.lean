-- Prove2me | solution 1 for GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:54.63792+00:00
-- url     : https://prove2.me/submissions/8022e5d4-42a9-47e1-a0aa-afca6e75de02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqOneOfNormOneValuationSubOneSmall
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqOneOfNormOneValuationSubOneSmallStatement
import Theorems.Thm_GlobalTheory_eq_one_of_norm_one_of_valuation_sub_one_le


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (ε : E) (w : HeightOneSpectrum (𝓞 E)) (K : ℕ), Module.finrank ℚ E < K → (∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1) → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ)) → ε = 1 := by
  first | exact @GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le | exact GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le | (intros; apply GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le <;> assumption)
end _root_.GlobalTheory.T
