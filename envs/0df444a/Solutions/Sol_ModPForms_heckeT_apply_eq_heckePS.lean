-- Prove2me | solution 1 for ModPForms.heckeT_apply_eq_heckePS
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/23e46bc2-72be-546d-839f-19f5520dc9e1

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_heckeT_apply_eq_heckePS

set_option autoImplicit false

theorem solution (F : Type) [Field F] (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (φ : PowerSeries F) :
    PowerSeries.heckeT ℓ k φ = ModPForms.heckePS (k : ℤ) ℓ φ := by
  ext n
  unfold ModPForms.heckePS
  rw [PowerSeries.coeff_heckeT, PowerSeries.coeff_mk, mul_comm ℓ n, mul_ite, mul_zero,
    show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]

end S_ModPForms_heckeT_apply_eq_heckePS
end P2MW
export P2MW.S_ModPForms_heckeT_apply_eq_heckePS (solution)
