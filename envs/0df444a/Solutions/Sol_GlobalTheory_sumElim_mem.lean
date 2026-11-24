-- Prove2me | solution 1 for GlobalTheory.sumElim_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:08.502199+00:00
-- url     : https://prove2.me/submissions/5e7c83e1-79eb-4eec-8d82-0545e36fcfda

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
variable {A S τ ι : Type*} [CommRing A] [CommRing S] [Algebra A S]
namespace GlobalTheory
theorem _root_.solution {K : Ideal S} {u : τ → S} {s : ι → S} (hu : ∀ k, u k ∈ K)
    (hs : ∀ i, s i ∈ K) : ∀ v, Sum.elim u s v ∈ K := by
  rintro (k | i)
  exacts [hu k, hs i]
end GlobalTheory
