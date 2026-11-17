-- Prove2me | solution 1 for N25.Endgame.exists_frobeniusLift25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:08.010208+00:00
-- url     : https://prove2.me/submissions/104beb1f-14db-4a41-b894-22a0a3613846

import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (D : RedDatum25 ℓ) :
    ∃ σ : N25.Gal, D.A.IsFrobeniusAt σ ℓ :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime Fact.out D.A D.hA

end N25.Endgame
