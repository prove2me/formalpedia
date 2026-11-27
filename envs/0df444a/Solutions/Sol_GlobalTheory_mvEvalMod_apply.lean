-- Prove2me | solution 1 for GlobalTheory.mvEvalMod_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:27.824739+00:00
-- url     : https://prove2.me/submissions/8144e76d-f3c5-46ff-8f91-c006ed0f0238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
namespace GlobalTheory
theorem _root_.solution (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) (n : ℕ)
    (f : MvPowerSeries σ A) :
    mvEvalMod A J x hx n f = Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) := rfl
end GlobalTheory
