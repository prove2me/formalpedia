-- Prove2me | solution 1 for GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:04.472087+00:00
-- url     : https://prove2.me/submissions/e4794027-d2ab-4e6a-a942-8c6c010e8294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonDenominatorOfValuationLeCofinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonDenominatorOfValuationLeCofiniteStatement
import Theorems.Thm_GlobalTheory_ValBoundDenom_exists_common_denominator_of_valuation_le


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)),
    (∀ᶠ w in Filter.cofinite, β w ≤ 1) → ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) → IsIntegral ℤ ((D : E) * x) := by
  first | exact @GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | exact GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | (intros; apply GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le <;> assumption)
end _root_.GlobalTheory.T
