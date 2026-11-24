-- Prove2me | solution 1 for GlobalTheory.Published.CMCurveGoodOutsidePrimeSt.exists_isGoodCMCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:46.835797+00:00
-- url     : https://prove2.me/submissions/15a734be-365c-41e8-b116-a2655f85d9a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ}
variable {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F}
namespace GlobalTheory.Published
namespace CMCurveGoodOutsidePrimeSt
theorem _root_.solution (h : CMCurveGoodOutsidePrimeSt)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) :
    ∃ (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F), IsGoodCMCurve p F A := by
  obtain ⟨F, -, A, hA, -⟩ := h p hp h4 h3
  exact ⟨F, A, hA⟩
end CMCurveGoodOutsidePrimeSt
end GlobalTheory.Published
