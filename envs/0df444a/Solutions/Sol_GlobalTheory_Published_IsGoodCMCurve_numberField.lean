-- Prove2me | solution 1 for GlobalTheory.Published.IsGoodCMCurve.numberField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:12.148551+00:00
-- url     : https://prove2.me/submissions/6ba49418-f5c6-4608-8d35-9c56cdab261d

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
theorem _root_.solution (h : IsGoodCMCurve p F A) : NumberField F := by
  obtain ⟨hF, -⟩ := h
  exact hF
end IsGoodCMCurve
end GlobalTheory.Published
