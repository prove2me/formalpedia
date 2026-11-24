-- Prove2me | solution 1 for GlobalTheory.Published.IsGoodCMCurve.j_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:50.878032+00:00
-- url     : https://prove2.me/submissions/55eef7a6-5581-43ca-9832-726d1e8feada

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
import Theorems.Thm_GlobalTheory_Published_IsIntegersLattice_j_eq

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
theorem _root_.solution [A.IsElliptic] (h : IsGoodCMCurve p F A) {L : PeriodPair}
    (hL : IsIntegersLattice p L) : (A.j : ℂ) = (latticeCurve L).j := by
  obtain ⟨_, _, L₀, hL₀, _, hj, _⟩ := h
  exact hj.trans (hL₀.j_eq hL)
end IsGoodCMCurve
end GlobalTheory.Published
