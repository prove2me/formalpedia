-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:02.846402+00:00
-- url     : https://prove2.me/submissions/f9be0af9-5168-4182-86e8-2c3c11f9b2f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPowStatement
import Theorems.Thm_GlobalTheory_QFam_isIntegral_value_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → IsIntegral R (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsIntegral R (f i τ₀ / Ω ^ w) := by
  first | exact @GlobalTheory.QFam.isIntegral_value_div | exact GlobalTheory.QFam.isIntegral_value_div | (intros; apply GlobalTheory.QFam.isIntegral_value_div <;> assumption)
end _root_.GlobalTheory.T
