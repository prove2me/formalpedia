-- Prove2me | solution 1 for ModularCurve.isMonicOfOrder_sharpUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/70dd16c7-4e83-58ee-9f2e-95c28b7d2dea

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isMonicOfOrder_sharpUnitSeries

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_isMonicOfOrder_sharpUnitSeries.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "etaProdPow constantCoeff_etaProdPow sharpUnitSeries sharpUnitSeries_def IsMonicOfOrder IsMonicOfOrder.single IsMonicOfOrder.ofPowerSeries IsMonicOfOrder.of_mul_right eisensteinNumerator qExpand"
p2m_open "ModularCurve"

namespace QexpN

private theorem isMonic_sharp (ℓ : ℕ) [NeZero ℓ] :
    IsMonicOfOrder (sharpUnitSeries ℓ) (-(eisensteinNumerator ℓ : ℤ)) := by
  set P : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) with hP
  have hPm : IsMonicOfOrder P 0 := IsMonicOfOrder.ofPowerSeries (constantCoeff_etaProdPow ℓ)
  have hQm : IsMonicOfOrder (qExpand ℚ ℓ P) 0 := by
    have h := hPm.qExpand ℓ
    rwa [mul_zero] at h
  have hQne : qExpand ℚ ℓ P ≠ 0 := hQm.ne_zero
  have hfg : IsMonicOfOrder (sharpUnitSeries ℓ * qExpand ℚ ℓ P)
      (-(eisensteinNumerator ℓ : ℤ)) := by
    have hcancel : sharpUnitSeries ℓ * qExpand ℚ ℓ P
        = HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) * P := by
      rw [sharpUnitSeries_def, ← hP, mul_assoc, inv_mul_cancel₀ hQne, mul_one]
    rw [hcancel]
    have h := (IsMonicOfOrder.single (-(eisensteinNumerator ℓ : ℤ))).mul hPm
    rwa [add_zero] at h
  have h := hfg.of_mul_right hQm
  rwa [sub_zero] at h

end QexpN

end ModularCurve

end

theorem solution (ℓ : ℕ) [NeZero ℓ] : ModularCurve.IsMonicOfOrder (ModularCurve.sharpUnitSeries ℓ) (-(ModularCurve.eisensteinNumerator ℓ : ℤ)) :=
  ModularCurve.QexpN.isMonic_sharp ℓ

end S_ModularCurve_isMonicOfOrder_sharpUnitSeries
end P2MW
export P2MW.S_ModularCurve_isMonicOfOrder_sharpUnitSeries (solution)
