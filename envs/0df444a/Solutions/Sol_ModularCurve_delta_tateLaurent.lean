-- Prove2me | solution 1 for ModularCurve.delta_tateLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e7286a1c-c0d5-5eb0-a2b6-1b68347eefa2

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_c4_tateLaurent
import Theorems.Thm_ModularCurve_c4_pow_three_tateLaurent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_delta_tateLaurent

set_option autoImplicit false

p2m_open "PowerSeries HahnSeries ModularCurve P2MW.S_ModularCurve_delta_tateLaurent.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "laurentOfInt laurentOfInt_apply tateLaurent jqModC eisenstein4 constantCoeff_eisenstein4 dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum c4_tateLaurent c4_pow_three_tateLaurent"
namespace TD2
p2m_open "ModularCurve"

theorem main (K : Type*) [CommRing K] :
    (tateLaurent K).Δ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) := by
  set L : PowerSeries ℤ →+* LaurentSeries K := laurentOfInt K with hL
  have hLapp : ∀ f, L f = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) f) := laurentOfInt_apply K

  have hc4 : (tateLaurent K).c₄ = L eisenstein4 := by rw [hLapp]; exact c4_tateLaurent K
  have hcube : (tateLaurent K).c₄ ^ 3 = jqModC K * (tateLaurent K).Δ := c4_pow_three_tateLaurent K
  have hj : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * L jNum := by rw [hLapp]; rfl
  have hjNum : jNum = eisenstein4 ^ 3 * dedekindEtaUnitInv := rfl
  have hinv : L dedekindEtaUnit * L dedekindEtaUnitInv = 1 := by
    rw [← map_mul, dedekindEtaUnit_mul_inv, map_one]
  have hsingle : HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.single (-1 : ℤ) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one]; rfl
  have hX : L PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : K) := by
    rw [hLapp, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

  have hunit : IsUnit (L eisenstein4 ^ 3) := by
    refine (IsUnit.map L ?_).pow 3
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_eisenstein4]
    exact isUnit_one

  have key : L eisenstein4 ^ 3 * L (PowerSeries.X * dedekindEtaUnit) = L eisenstein4 ^ 3 * (tateLaurent K).Δ := by
    have h := hcube
    rw [hc4, hj, hjNum, map_mul, map_pow] at h

    calc L eisenstein4 ^ 3 * L (PowerSeries.X * dedekindEtaUnit)
        = (HahnSeries.single (-1 : ℤ) (1 : K) * (L eisenstein4 ^ 3 * L dedekindEtaUnitInv) * (tateLaurent K).Δ)
            * (HahnSeries.single (1 : ℤ) (1 : K) * L dedekindEtaUnit) := by rw [← h, map_mul, hX]
      _ = L eisenstein4 ^ 3 * (tateLaurent K).Δ *
            ((HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.single (-1 : ℤ) (1 : K)) *
              (L dedekindEtaUnit * L dedekindEtaUnitInv)) := by ring
      _ = L eisenstein4 ^ 3 * (tateLaurent K).Δ := by rw [hsingle, hinv, mul_one, mul_one]
  have := hunit.mul_left_cancel key
  rw [← this, hLapp]

end ModularCurve.TD2

open PowerSeries HahnSeries in
theorem solution (K : Type*) [CommRing K] :
    (tateLaurent K).Δ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) :=
  ModularCurve.TD2.main K

end S_ModularCurve_delta_tateLaurent
end P2MW
export P2MW.S_ModularCurve_delta_tateLaurent (solution)
