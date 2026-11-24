-- Prove2me | solution 1 for GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:41.723297+00:00
-- url     : https://prove2.me/submissions/31b72762-1e84-44b9-9383-683520858e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsPowValuationDivSubOneLeOfCongr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsPowValuationDivSubOneLeOfCongrStatement
import Theorems.Thm_GlobalTheory_exists_pow_valuation_div_sub_one_le


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 → ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N → v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_pow_valuation_div_sub_one_le | exact GlobalTheory.exists_pow_valuation_div_sub_one_le | (intros; apply GlobalTheory.exists_pow_valuation_div_sub_one_le <;> assumption)
end _root_.GlobalTheory.T
