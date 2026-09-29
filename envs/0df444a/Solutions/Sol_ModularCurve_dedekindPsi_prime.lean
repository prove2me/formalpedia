-- Prove2me | solution 1 for ModularCurve.dedekindPsi_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9568acc4-f330-51e3-a30f-5aca4d5d65a3

import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=by
  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [hp.squarefree, Nat.div_self hp.pos]

end

end S_ModularCurve_dedekindPsi_prime
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_prime (solution)
