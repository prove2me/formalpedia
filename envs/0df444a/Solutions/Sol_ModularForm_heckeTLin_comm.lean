-- Prove2me | solution 1 for ModularForm.heckeTLin_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4e770cd4-2206-5816-abbb-8997bfbda8a2

import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_heckeT_heckeT_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_heckeTLin_comm

theorem solution {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (ModularForm.heckeTLin k hp hpN) (ModularForm.heckeTLin k hq hqN) := by
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  · rw [commute_iff_eq]; ext f τ
    simpa using congrFun (ModularFormClass.heckeT_heckeT_comm f (by simp)
      ((Nat.coprime_primes hp hq).mpr hpq)) τ

end S_ModularForm_heckeTLin_comm
end P2MW
export P2MW.S_ModularForm_heckeTLin_comm (solution)
