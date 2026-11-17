-- Prove2me | solution 1 for N25.Endgame.cusp_zero_reduction_fixed_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:04.55371+00:00
-- url     : https://prove2.me/submissions/f6ea8c73-412f-4ff1-90c0-9b221f3ace30

import Mathlib
import Theorems.Thm_N25_Endgame_cusp_zero_reduces_qInfinity_good
import Definitions.Def_N25_CuspReduction
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_Endgame_qInfinity_frobenius_fixed

set_option autoImplicit false

namespace N25.Endgame

/-- The selected cusp reduction is fixed by Frobenius at both good small primes. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (D : RedDatum25 p) :
    frobPlace25 D (redPlace25 D (pG25 0)) = redPlace25 D (pG25 0) := by
  rw [cusp_zero_reduces_qInfinity_good p hp D]
  exact qInfinity_frobenius_fixed p D

end N25.Endgame
