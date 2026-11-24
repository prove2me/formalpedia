-- Prove2me | solution 1 for GlobalTheory.CompactRep.isCompactOperator_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:28.080997+00:00
-- url     : https://prove2.me/submissions/efa830fd-6d8d-414d-b030-be2af3c97a94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
import Theorems.Thm_GlobalTheory_CompactRep_convex_compactOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}
namespace GlobalTheory.CompactRep
theorem _root_.solution [IsProbabilityMeasure μ] {F : X → H →L[ℂ] H}
    (hFi : Integrable F μ) (hF : ∀ k, IsCompactOperator (F k)) :
    IsCompactOperator (∫ k, F k ∂μ : H →L[ℂ] H) := by
  have hs : IsClosed {f : H →L[ℂ] H | IsCompactOperator f} := isClosed_setOfPred_isCompactOperator
  have hc : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := convex_compactOperators
  have hae : ∀ᵐ k ∂μ, F k ∈ {f : H →L[ℂ] H | IsCompactOperator f} := Filter.Eventually.of_forall hF
  have hm := hc.integral_mem hs hae hFi
  exact hm
end GlobalTheory.CompactRep
