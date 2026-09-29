-- Prove2me | solution 1 for ModularForm.coeffHeckeU_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9bcfe419-66f1-5a91-a23b-d098cc6ba100

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_coeffHeckeU_int

set_option autoImplicit false

open ModularForm

theorem solution (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeU p a n = m := by
  rw [coeffHeckeU_apply]
  exact ha (n * p)

end S_ModularForm_coeffHeckeU_int
end P2MW
export P2MW.S_ModularForm_coeffHeckeU_int (solution)
