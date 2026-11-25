-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_denominator_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:20:10.033403+00:00
-- url     : https://prove2.me/submissions/5e811620-bd9c-4d4d-a440-53addfa30ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitDenominatorIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitDenominatorIntegralStatement
import Theorems.Thm_GlobalTheory_exists_unit_at_prime_mul_integral


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
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) → ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  first | exact @GlobalTheory.exists_unit_at_prime_mul_integral | exact GlobalTheory.exists_unit_at_prime_mul_integral | (intros; apply GlobalTheory.exists_unit_at_prime_mul_integral <;> assumption)
end _root_.GlobalTheory.T
