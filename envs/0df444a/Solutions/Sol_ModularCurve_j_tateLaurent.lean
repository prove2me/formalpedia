-- Prove2me | solution 1 for ModularCurve.j_tateLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/245a1662-1eab-5e53-927c-fe88f772de64

import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_ModularCurve_eisenstein4_cube_sub_mk_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_j_tateLaurent

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "tateB twelve_mul_tateB tateA4 tateA6 eisenstein6 coeff_tateA4 coeff_tateA6 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ tatePowerSeries_a₆ laurentOfInt laurentOfInt_apply tateLaurent jqModC jqNModC jqModC_rat qExpand eisenstein4 dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jq eisenstein4_cube_sub_mk_sq"
p2m_open "ModularCurve"

theorem c₄_tatePowerSeries_eq_one_sub :
    tatePowerSeries.c₄ = 1 - PowerSeries.C 48 * tateA4 := by
  rw [show (PowerSeries.C (48 : ℤ)) = (48 : PowerSeries ℤ) from map_ofNat _ 48]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tatePowerSeries_a₁,
    tatePowerSeries_a₂, tatePowerSeries_a₃, tatePowerSeries_a₄]
  ring

theorem c₆_tatePowerSeries_eq :
    tatePowerSeries.c₆ = -1 + PowerSeries.C 72 * tateA4 - PowerSeries.C 864 * tateA6 := by
  rw [show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72,
    show (PowerSeries.C (864 : ℤ)) = (864 : PowerSeries ℤ) from map_ofNat _ 864]
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃, tatePowerSeries_a₄,
    tatePowerSeries_a₆]
  ring

theorem c₄_tatePowerSeries : tatePowerSeries.c₄ = eisenstein4 := by
  rw [c₄_tatePowerSeries_eq_one_sub]
  ext n
  rw [eisenstein4, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    coeff_tateA4]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [if_neg hn.ne', mul_neg, Finset.mul_sum]
    rw [show (∑ d ∈ n.divisors, (48 : ℤ) * (5 * (d : ℤ) ^ 3))
        = ∑ d ∈ n.divisors, 240 * (d : ℤ) ^ 3 from
      Finset.sum_congr rfl fun d _ => by ring]
    ring

theorem c₆_tatePowerSeries : tatePowerSeries.c₆ = -eisenstein6 := by
  rw [c₆_tatePowerSeries_eq]
  ext n
  rw [map_neg, eisenstein6, PowerSeries.coeff_mk, map_sub, map_add, map_neg,
    PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_tateA4,
    coeff_tateA6]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [if_neg hn.ne', mul_neg, neg_zero, zero_add, sub_neg_eq_add, Finset.mul_sum]
    have hSb : (∑ d ∈ n.divisors, (864 : ℤ) * tateB d)
        = (∑ d ∈ n.divisors, 72 * (5 * (d : ℤ) ^ 3)) + ∑ d ∈ n.divisors, 504 * (d : ℤ) ^ 5 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      have h := twelve_mul_tateB d
      linarith
    have hE6 : (∑ d ∈ n.divisors, (-504 : ℤ) * (d : ℤ) ^ 5)
        = -∑ d ∈ n.divisors, 504 * (d : ℤ) ^ 5 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    linarith [hSb, hE6]

theorem eisenstein4_cube_sub_eisenstein6_sq :
    eisenstein4 ^ 3 - eisenstein6 ^ 2 = 1728 * (PowerSeries.X * dedekindEtaUnit) :=
  eisenstein4_cube_sub_mk_sq

theorem jqModC_eq_single_mul_laurentOfInt (K : Type*) [CommRing K] :
    jqModC K = HahnSeries.single (-1 : ℤ) 1 * laurentOfInt K jNum := rfl

theorem single_neg_one_mul_laurentOfInt_X (K : Type*) [CommRing K] :
    (HahnSeries.single (-1 : ℤ) (1 : K)) * laurentOfInt K PowerSeries.X = 1 := by
  rw [laurentOfInt_apply, PowerSeries.map_X, ofPowerSeries_X, single_mul_single,
    neg_add_cancel, mul_one, single_zero_one]

theorem laurentOfInt_dedekindEtaUnitInv_mul (K : Type*) [CommRing K] :
    laurentOfInt K dedekindEtaUnitInv * laurentOfInt K dedekindEtaUnit = 1 := by
  rw [← map_mul, mul_comm, dedekindEtaUnit_mul_inv, map_one]

theorem Δ_tatePowerSeries :
    tatePowerSeries.Δ = PowerSeries.X * dedekindEtaUnit := by
  have hc : (1728 : PowerSeries ℤ) * tatePowerSeries.Δ
      = 1728 * (PowerSeries.X * dedekindEtaUnit) := by
    rw [WeierstrassCurve.c_relation, c₄_tatePowerSeries, c₆_tatePowerSeries, neg_pow,
      neg_one_pow_two, one_mul, eisenstein4_cube_sub_eisenstein6_sq]
  have h1728 : (1728 : PowerSeries ℤ) ≠ 0 := fun h => by
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this; exact absurd this (by decide)
  exact mul_left_cancel₀ h1728 hc

theorem c₄_pow_three_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ ^ 3 = jqModC K * (tateLaurent K).Δ := by
  rw [tateLaurent, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, c₄_tatePowerSeries,
    Δ_tatePowerSeries, ← map_pow, jqModC_eq_single_mul_laurentOfInt,
    show jNum = eisenstein4 ^ 3 * dedekindEtaUnitInv from rfl, map_mul, map_mul]
  calc laurentOfInt K (eisenstein4 ^ 3)
      = laurentOfInt K (eisenstein4 ^ 3)
          * (laurentOfInt K dedekindEtaUnitInv * laurentOfInt K dedekindEtaUnit)
          * (single (-1 : ℤ) (1 : K) * laurentOfInt K PowerSeries.X) := by
        rw [laurentOfInt_dedekindEtaUnitInv_mul, single_neg_one_mul_laurentOfInt_X,
          mul_one, mul_one]
    _ = single (-1 : ℤ) 1 * (laurentOfInt K (eisenstein4 ^ 3) * laurentOfInt K dedekindEtaUnitInv)
          * (laurentOfInt K PowerSeries.X * laurentOfInt K dedekindEtaUnit) := by ring

private theorem j_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).j = jqModC K := by
  rw [WeierstrassCurve.j, c₄_pow_three_tateLaurent K, ← WeierstrassCurve.coe_Δ',
    mul_comm (jqModC K), Units.inv_mul_cancel_left]

theorem j_tateLaurent_rat : (tateLaurent ℚ).j = jq := by
  rw [j_tateLaurent ℚ, jqModC_rat]

private theorem j_map_qExpand_tateLaurent (K : Type*) [CommRing K] (N : ℕ) [NeZero N] :
    ((tateLaurent K).map (qExpand K N)).j = jqNModC K N := by
  rw [WeierstrassCurve.map_j, j_tateLaurent K, jqNModC]

end ModularCurve

end

namespace ModularCurve
p2m_export "ModularCurve" "tateB twelve_mul_tateB tateA4 tateA6 eisenstein6 coeff_tateA4 coeff_tateA6 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ tatePowerSeries_a₆ laurentOfInt laurentOfInt_apply tateLaurent jqModC jqNModC jqModC_rat qExpand eisenstein4 dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jq eisenstein4_cube_sub_mk_sq"
p2m_open "ModularCurve"

private theorem Delta_tatePowerSeries :
    tatePowerSeries.Δ = PowerSeries.X * dedekindEtaUnit :=
  Δ_tatePowerSeries

private theorem c4_pow_three_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ ^ 3 = jqModC K * (tateLaurent K).Δ :=
  c₄_pow_three_tateLaurent K

end ModularCurve

open PowerSeries HahnSeries _root_.ModularCurve _root_.P2MW.S_ModularCurve_j_tateLaurent.ModularCurve in

theorem solution (K : Type*) [CommRing K] :
    (tateLaurent K).j = jqModC K :=
  ModularCurve.j_tateLaurent K

#print axioms solution

end S_ModularCurve_j_tateLaurent
end P2MW
export P2MW.S_ModularCurve_j_tateLaurent (solution)
