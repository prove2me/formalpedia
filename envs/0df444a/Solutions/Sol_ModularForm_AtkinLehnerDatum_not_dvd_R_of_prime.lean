-- Prove2me | solution 1 for ModularForm.AtkinLehnerDatum.not_dvd_R_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b260e7d0-f143-5279-8ca0-abbaf6803456

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime

set_option autoImplicit false

theorem solution {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) :
    ¬ q ∣ W.R := by
  intro ⟨c, hc⟩
  have h1 : (q : ℤ) ∣ 1 := ⟨W.a - (c : ℤ) * W.b, by
    have hb := W.bezout; rw [hc] at hb; push_cast at hb; linarith⟩
  have hq1 : q = 1 := by
    have := Int.isUnit_iff.mp (isUnit_of_dvd_one h1)
    omega
  exact absurd hq1 hq.one_lt.ne'

end S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime
end P2MW
export P2MW.S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime (solution)
