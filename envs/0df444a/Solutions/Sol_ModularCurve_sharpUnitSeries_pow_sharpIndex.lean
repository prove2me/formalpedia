-- Prove2me | solution 1 for ModularCurve.sharpUnitSeries_pow_sharpIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3fd51d8f-c2e1-5d16-b05f-563baf9dd194

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitSeries_pow_sharpIndex

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_sharpUnitSeries_pow_sharpIndex.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "sharpIndex sharpExp_mul_sharpIndex sharpIndex_mul_eisensteinNumerator etaProdPow constantCoeff_etaProdPow sharpUnitSeries sharpUnitSeries_def IsMonicOfOrder IsMonicOfOrder.ofPowerSeries dedekindEtaUnitQ deltaSeries deltaSeriesN isMonicOfOrder_deltaSeriesN modularUnitSeries eisensteinNumerator qExpand qExpand_single etaProd"
p2m_open "ModularCurve"

namespace QexpN

private theorem sharp_pow (ℓ : ℕ) [NeZero ℓ] :
    sharpUnitSeries ℓ ^ sharpIndex ℓ = modularUnitSeries ℓ := by
  set P : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) with hP
  set D : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ dedekindEtaUnitQ with hD

  have hPk : P ^ sharpIndex ℓ = D := by
    rw [hP, hD, ← map_pow, etaProdPow, ← map_pow, ← pow_mul, sharpExp_mul_sharpIndex]
    rfl

  have hPm : IsMonicOfOrder P 0 := IsMonicOfOrder.ofPowerSeries (constantCoeff_etaProdPow ℓ)
  have hQm : IsMonicOfOrder (qExpand ℚ ℓ P) 0 := by
    have h := hPm.qExpand ℓ
    rwa [mul_zero] at h
  have hQne : qExpand ℚ ℓ P ≠ 0 := hQm.ne_zero
  have hdsN : deltaSeriesN ℓ ≠ 0 := (isMonicOfOrder_deltaSeriesN ℓ).ne_zero

  have hdsN_eq : deltaSeriesN ℓ
      = HahnSeries.single ((ℓ : ℤ)) (1 : ℚ) * qExpand ℚ ℓ D := by
    rw [deltaSeriesN, deltaSeries, map_mul, qExpand_single, mul_one]

  have harith : (sharpIndex ℓ) • (-(eisensteinNumerator ℓ : ℤ)) + (ℓ : ℤ) = 1 := by
    have h := sharpIndex_mul_eisensteinNumerator ℓ
    have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)
    have hcast : ((sharpIndex ℓ * eisensteinNumerator ℓ : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by
      rw [h, Nat.cast_sub hℓ1, Nat.cast_one]
    push_cast at hcast
    rw [nsmul_eq_mul]
    linarith

  have hQPk : qExpand ℚ ℓ P ^ sharpIndex ℓ = qExpand ℚ ℓ D := by
    rw [← map_pow, hPk]

  rw [modularUnitSeries, eq_mul_inv_iff_mul_eq₀ hdsN]
  calc sharpUnitSeries ℓ ^ sharpIndex ℓ * deltaSeriesN ℓ
      = (HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) ^ sharpIndex ℓ
          * P ^ sharpIndex ℓ * ((qExpand ℚ ℓ P)⁻¹) ^ sharpIndex ℓ)
        * (HahnSeries.single ((ℓ : ℤ)) (1 : ℚ) * qExpand ℚ ℓ D) := by
        rw [sharpUnitSeries_def, ← hP, mul_pow, mul_pow, hdsN_eq]
    _ = (HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) ^ sharpIndex ℓ
          * HahnSeries.single ((ℓ : ℤ)) (1 : ℚ)) * D
        * ((qExpand ℚ ℓ P ^ sharpIndex ℓ)⁻¹ * qExpand ℚ ℓ D) := by
        rw [hPk, ← inv_pow]
        ring
    _ = (HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) ^ sharpIndex ℓ
          * HahnSeries.single ((ℓ : ℤ)) (1 : ℚ)) * D * 1 := by
        rw [hQPk, inv_mul_cancel₀]
        rw [← hQPk]
        exact pow_ne_zero _ hQne
    _ = HahnSeries.single (1 : ℤ) (1 : ℚ) * D := by
        rw [mul_one, HahnSeries.single_pow, one_pow, HahnSeries.single_mul_single, one_mul,
          harith]
    _ = deltaSeries := by rw [deltaSeries, hD]

end QexpN

end ModularCurve

end

theorem solution (ℓ : ℕ) [NeZero ℓ] : ModularCurve.sharpUnitSeries ℓ ^ ModularCurve.sharpIndex ℓ = ModularCurve.modularUnitSeries ℓ :=
  ModularCurve.QexpN.sharp_pow ℓ

end S_ModularCurve_sharpUnitSeries_pow_sharpIndex
end P2MW
export P2MW.S_ModularCurve_sharpUnitSeries_pow_sharpIndex (solution)
