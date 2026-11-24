-- Prove2me | solution 1 for GlobalTheory.DI.FrobDeriv.twist_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:20.246254+00:00
-- url     : https://prove2.me/submissions/085013d2-e12c-420e-a14a-feb0e5cc4f6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.FrobDeriv
variable {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime]
  [CharP K p]
namespace GlobalTheory.DI.FrobDeriv
theorem _root_.solution (c : K) (m : FrobTwist K p M) :
    c • m = (c ^ p • (show M from m) : M) := by
  show (frobenius K p c) • (show M from m) = _
  rw [frobenius_def]
end GlobalTheory.DI.FrobDeriv
