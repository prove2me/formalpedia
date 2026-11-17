-- Prove2me | solution 1 for N25.Endgame.redPlace25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:16.620706+00:00
-- url     : https://prove2.me/submissions/b1379b29-e987-4d6a-832c-874d2d49d04f

import Definitions.Def_N25_Endgame

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (D : RedDatum25 ℓ) (P : GPlace) :
    (redPlace25 D P).deg = P.deg :=
  (ModularCurve.isPlaceReductionQExpModL_placeReductionQExpModL D.hred).1 P

end N25.Endgame
