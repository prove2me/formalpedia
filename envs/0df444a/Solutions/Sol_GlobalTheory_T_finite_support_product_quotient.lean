-- Prove2me | solution 1 for GlobalTheory.T.finite_support_product_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:36.296089+00:00
-- url     : https://prove2.me/submissions/cf8d6b96-45aa-450c-b948-962268cd6bba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportProductQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportProductQuotientStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdQuotient_support_mul_out_finite


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
theorem _root_.solution : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite → (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite → (∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) → (∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) → (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  first | exact @GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | exact GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | (intros; apply GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite <;> assumption)
end _root_.GlobalTheory.T
