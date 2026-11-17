-- Prove2me | solution 1 for N25.Endgame.coe_redM25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:11.997813+00:00
-- url     : https://prove2.me/submissions/bf46bb17-a5fe-4746-a814-303d62aea7d6

import Definitions.Def_N25_ReductionMap
import Theorems.Thm_N25_Endgame_red_mem_fixed25
import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt

set_option autoImplicit false

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) (z : ↥N25.M) :
    ((redM25 hℓ25 D z : RedFixed25 D) : SpecialPic D.A) = red25 D z := by
  rw [redM25, dif_pos (show ∀ z : ↥N25.M, ((red25 D).comp N25.M.subtype) z ∈ RedFixed25 D from
    fun z => red_mem_fixed25 hℓ25 D z z.property)]
  rfl

end N25.Endgame
