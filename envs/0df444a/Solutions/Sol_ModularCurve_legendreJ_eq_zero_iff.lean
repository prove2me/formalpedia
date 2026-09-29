-- Prove2me | solution 1 for ModularCurve.legendreJ_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c7abd80b-209d-5921-929d-dcc92a704416

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_legendreJ_eq_zero_iff

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

theorem legendreJ_eq_zero_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  rw [legendreJ, div_eq_zero_iff, or_iff_left hden, mul_eq_zero, or_iff_right (pow_ne_zero _ h2)]
  exact pow_eq_zero_iff three_ne_zero

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_zero_iff.ModularCurve"

theorem solution {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 :=
  ModularCurve.legendreJ_eq_zero_iff' h2 ht0 ht1

end S_ModularCurve_legendreJ_eq_zero_iff
end P2MW
export P2MW.S_ModularCurve_legendreJ_eq_zero_iff (solution)
