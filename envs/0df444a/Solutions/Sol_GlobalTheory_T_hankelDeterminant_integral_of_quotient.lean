-- Prove2me | solution 1 for GlobalTheory.T.hankelDeterminant_integral_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:43.615835+00:00
-- url     : https://prove2.me/submissions/07eae5b5-37d3-4bda-a64d-0bf674015aab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HankelDeterminantIntegralOfQuotient
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HankelDeterminantIntegralOfQuotientStatement
import Theorems.Thm_GlobalTheory_Nef_hankel_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  first | exact @GlobalTheory.Nef.hankel_integral | exact GlobalTheory.Nef.hankel_integral | (intros; apply GlobalTheory.Nef.hankel_integral <;> assumption)
end _root_.GlobalTheory.T
