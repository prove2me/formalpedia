-- Prove2me | solution 1 for GlobalTheory.QFam.fam_value_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:13:05.388258+00:00
-- url     : https://prove2.me/submissions/6cb6f1e8-412e-400a-8979-7cc9c8433593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfIsIntegralAlgebraicNumbers
import Theorems.Thm_GlobalTheory_QFam_isAlgebraic_of_isIntegral_algebraicNumbers
import Theorems.Thm_GlobalTheory_T_isIntegral_modularFamily_value_div_period_pow


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
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (IsAlgebraic ℚ) N (f i)) → IsAlgebraic ℚ (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsAlgebraic ℚ (f i τ₀ / Ω ^ w) := by
  intro ι _ act w N f τ₀ Ω hN hb hf hq hj hΩ i
  refine isAlgebraic_of_isIntegral_algebraicNumbers
    (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N f (integralClosure ℚ ℂ).toSubring τ₀ Ω hN hb hf (fun k => ?_) ?_ hΩ i)
  · obtain ⟨a, ha, hal⟩ := hq k
    exact ⟨a, ha, fun n => (hal n).isIntegral⟩
  · exact isIntegral_algebraMap (R := (integralClosure ℚ ℂ).toSubring) (A := ℂ)
      (x := ⟨jT τ₀, hj.isIntegral⟩)
end GlobalTheory.QFam
