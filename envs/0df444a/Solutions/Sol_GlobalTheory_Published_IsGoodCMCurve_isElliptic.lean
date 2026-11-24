-- Prove2me | solution 1 for GlobalTheory.Published.IsGoodCMCurve.isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:44.453139+00:00
-- url     : https://prove2.me/submissions/fbaa7c5e-211d-4123-845d-e4a52ea12a02

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
theorem _root_.solution (h : IsGoodCMCurve p F A) : A.IsElliptic := by
  obtain ⟨-, hA, -⟩ := h
  exact hA
end IsGoodCMCurve
end GlobalTheory.Published
