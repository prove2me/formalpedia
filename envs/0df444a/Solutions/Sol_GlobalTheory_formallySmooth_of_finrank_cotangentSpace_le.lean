-- Prove2me | solution 1 for GlobalTheory.formallySmooth_of_finrank_cotangentSpace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:30.575093+00:00
-- url     : https://prove2.me/submissions/5b11bbaf-b34f-44b5-9acf-312881fb81ac

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (k S : Type*) [Field k] [PerfectField k]
    [CommRing S] [IsLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] {d : ℕ}
    (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim S)
    (h₂ : Module.finrank (ResidueField S) (CotangentSpace S) ≤ d) :
    Algebra.FormallySmooth k S :=
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing k S
  have := (isRegularLocalRing_of_finrank_cotangentSpace_le S h₁ h₂).1
  formallySmooth_of_isRegularLocalRing_of_perfectField k S
end GlobalTheory
