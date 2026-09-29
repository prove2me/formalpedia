-- Prove2me | solution 1 for ModularCurve.jqNModC_pow_eq_jqNModC_mul_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e1a21f2b-7db9-5655-8bfc-624638cc409a

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP

set_option autoImplicit false

open ModularCurve

theorem solution
    (K : Type) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] (n : ℕ) [NeZero n] [NeZero (q * n)] :
    (jqNModC K n) ^ q = jqNModC K (q * n) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero (n * q) := ⟨by rw [mul_comm]; exact NeZero.ne (q * n)⟩
  have h1 : jqNModC K q = (jqModC K) ^ q := ModularCurve.frobenius_identity_geom_unconditional K
  calc (jqNModC K n) ^ q = qExpand K n ((jqModC K) ^ q) := by rw [jqNModC, map_pow]
    _ = qExpand K n (qExpand K q (jqModC K)) := by rw [← h1, jqNModC]
    _ = qExpand K (n * q) (jqModC K) := by rw [qExpand_qExpand]
    _ = jqNModC K (q * n) := by rw [jqNModC, qExpand_congr (mul_comm n q)]

end S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP
end P2MW
export P2MW.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP (solution)
