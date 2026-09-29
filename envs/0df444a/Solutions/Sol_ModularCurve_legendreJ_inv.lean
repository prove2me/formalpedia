-- Prove2me | solution 1 for ModularCurve.legendreJ_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2ccc3435-3512-54ef-b5be-91d01d646e42

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_legendreJ_inv

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

theorem legendreJ_inv' {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [inv_zero]
  have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have hu : (t⁻¹ : K) ≠ 0 := inv_ne_zero ht
  have e1 : (t⁻¹ ^ 2 - t⁻¹ + 1) ^ 3 = (t ^ 2 - t + 1) ^ 3 * t⁻¹ ^ 6 := by
    linear_combination (-t^5*t⁻¹^5 + 3*t^4*t⁻¹^5 - t^4*t⁻¹^4 - 6*t^3*t⁻¹^5 + 3*t^3*t⁻¹^4 - t^3*t⁻¹^3 + 7*t^2*t⁻¹^5 - 6*t^2*t⁻¹^4 + 3*t^2*t⁻¹^3 - t^2*t⁻¹^2 - 6*t*t⁻¹^5 + 7*t*t⁻¹^4 - 6*t*t⁻¹^3 + 3*t*t⁻¹^2 - t*t⁻¹ + 3*t⁻¹^5 - 6*t⁻¹^4 + 7*t⁻¹^3 - 6*t⁻¹^2 + 3*t⁻¹ - 1) * hi
  have e2 : t⁻¹ ^ 2 * (t⁻¹ - 1) ^ 2 = (t ^ 2 * (t - 1) ^ 2) * t⁻¹ ^ 6 := by
    linear_combination (-t^3*t⁻¹^5 + 2*t^2*t⁻¹^5 - t^2*t⁻¹^4 - t*t⁻¹^5 + 2*t*t⁻¹^4 - t*t⁻¹^3 - t⁻¹^4 + 2*t⁻¹^3 - t⁻¹^2) * hi
  simp only [legendreJ]
  rw [e1, e2, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero 6 hu)]

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_inv.ModularCurve"

theorem solution {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t :=
  ModularCurve.legendreJ_inv' t

end S_ModularCurve_legendreJ_inv
end P2MW
export P2MW.S_ModularCurve_legendreJ_inv (solution)
