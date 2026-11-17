-- Prove2me | solution 1 for N25.Endgame.red_mem_fixed25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:11.251301+00:00
-- url     : https://prove2.me/submissions/afae15b3-0424-4a67-b08a-e58dd515e96e

import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_Endgame_exists_frobeniusLift25
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) (z : N25.J) (hz : z ∈ N25.M) :
    red25 D z ∈ RedFixed25 D := by
  obtain ⟨σ, hσ⟩ := exists_frobeniusLift25 D
  change frobPic25 D (red25 D z) - red25 D z = 0
  apply sub_eq_zero.mpr
  have h := ModularCurve.reductionQExpModL_gammaH_smul_of_isFrobeniusAt
    25 N25.H25 hℓ25 D.A D.hA D.hred σ hσ z
  change ∀ σ : N25.Gal, σ • z = z at hz
  rw [hz σ] at h
  exact h.symm

end N25.Endgame
