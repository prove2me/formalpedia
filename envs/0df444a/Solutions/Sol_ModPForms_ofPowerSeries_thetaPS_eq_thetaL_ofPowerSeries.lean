-- Prove2me | solution 1 for ModPForms.ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3803adcc-553d-53b0-8aa6-b2ba63d3d995

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (ModPForms.thetaPS φ) =
      ModularCurve.thetaL K (HahnSeries.ofPowerSeries ℤ K φ) := by
  ext n
  rw [ModularCurve.thetaL_apply, LaurentSeries.derivative_apply, ← sub_add_cancel n 1,
    HahnSeries.coeff_single_mul_add, LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, one_mul,
    Ring.choose_one_right]
  change ((ModPForms.thetaPS φ : PowerSeries K) : LaurentSeries K).coeff n =
    n • ((φ : PowerSeries K) : LaurentSeries K).coeff n
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [smul_zero]
  · rw [ModPForms.thetaPS, PowerSeries.coeff_mk, zsmul_eq_mul]
    congr 1
    have h1 : ((n.natAbs : ℤ) : K) = ((n : ℤ) : K) := by rw [Int.natAbs_of_nonneg (not_lt.mp hn)]
    rw [Int.cast_natCast] at h1
    exact h1

end S_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
end P2MW
export P2MW.S_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries (solution)
