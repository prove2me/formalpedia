-- Prove2me | solution 1 for ModularCurve.eisensteinNumerator_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/53997de1-871f-5dd8-880c-d794c32141db

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinNumerator_coprime

open ModularCurve

theorem solution (p : ℕ) (hp : p ≠ 0) : (eisensteinNumerator p).Coprime p := by
  refine Nat.Coprime.coprime_dvd_left (eisensteinNumerator_dvd p) ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.succ_sub_one, Nat.succ_eq_add_one]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)

end S_ModularCurve_eisensteinNumerator_coprime
end P2MW
export P2MW.S_ModularCurve_eisensteinNumerator_coprime (solution)
