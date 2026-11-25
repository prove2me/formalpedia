-- Prove2me | solution 1 for GlobalTheory.Published.IsGoodCMCurve.hasGoodReductionOutside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:14.735966+00:00
-- url     : https://prove2.me/submissions/fe046273-befa-4d7c-8dd1-f705d013e0be

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
namespace IsGoodCMCurve
theorem _root_.solution [NumberField F] (h : IsGoodCMCurve p F A) :
    HasGoodReductionOutside p A := by
  obtain ⟨_, _, L₀, _, _, _, hg⟩ := h
  exact hg
end IsGoodCMCurve
end GlobalTheory.Published
