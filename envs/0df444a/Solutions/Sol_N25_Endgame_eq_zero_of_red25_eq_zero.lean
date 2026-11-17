-- Prove2me | solution 1 for N25.Endgame.eq_zero_of_red25_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:19.454786+00:00
-- url     : https://prove2.me/submissions/dae77fd3-9311-4038-a721-5d2378209cb5

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) (m : ℕ) (hm : ¬ ℓ ∣ m)
    (z : N25.J) (hmz : m • z = 0) (hz : red25 D z = 0) :
    z = 0 :=
  ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
    25 N25.H25 hℓ25 D.A D.hA D.hred m hm z hmz hz

end N25.Endgame
