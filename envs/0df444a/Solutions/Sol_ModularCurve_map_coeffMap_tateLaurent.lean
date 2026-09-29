-- Prove2me | solution 1 for ModularCurve.map_coeffMap_tateLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0e2011de-9849-5f9c-8c89-5a7ef13f0a4c

import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_coeffMap_tateLaurent

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "tateB twelve_mul_tateB tateA4 tateA6 eisenstein6 coeff_tateA4 coeff_tateA6 coeff_zero_tateA4 coeff_zero_tateA6 constantCoeff_tateA4 constantCoeff_tateA6 coeff_one_tateA4 coeff_one_tateA6 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ tatePowerSeries_a₆ laurentOfInt laurentOfInt_apply tateLaurent eisenstein4 ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffEmb"
p2m_open "ModularCurve"

theorem tateB_one : tateB 1 = 1 := by norm_num [tateB]

theorem tateB_two : tateB 2 = 22 := by norm_num [tateB]

theorem coeff_two_tateA4 : PowerSeries.coeff 2 tateA4 = -45 := by
  rw [coeff_tateA4, Nat.Prime.divisors Nat.prime_two,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num

theorem coeff_two_tateA6 : PowerSeries.coeff 2 tateA6 = -23 := by
  rw [coeff_tateA6, Nat.Prime.divisors Nat.prime_two,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), tateB_one, tateB_two]
  norm_num

theorem coeff_one_eisenstein6 : PowerSeries.coeff 1 eisenstein6 = -504 := by
  rw [eisenstein6, PowerSeries.coeff_mk]
  norm_num [Nat.divisors_one]

theorem coeff_two_eisenstein6 : PowerSeries.coeff 2 eisenstein6 = -16632 := by
  rw [eisenstein6, PowerSeries.coeff_mk, if_neg (by norm_num), Nat.Prime.divisors Nat.prime_two,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num

theorem tateLaurent_a₁ (K : Type*) [CommRing K] : (tateLaurent K).a₁ = 1 := by
  rw [tateLaurent, WeierstrassCurve.map_a₁, tatePowerSeries_a₁, map_one]

theorem tateLaurent_a₂ (K : Type*) [CommRing K] : (tateLaurent K).a₂ = 0 := by
  rw [tateLaurent, WeierstrassCurve.map_a₂, tatePowerSeries_a₂, map_zero]

theorem tateLaurent_a₃ (K : Type*) [CommRing K] : (tateLaurent K).a₃ = 0 := by
  rw [tateLaurent, WeierstrassCurve.map_a₃, tatePowerSeries_a₃, map_zero]

theorem Δ_tatePowerSeries_eq :
    tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
  rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
    show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
    show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
    tatePowerSeries_a₄, tatePowerSeries_a₆]
  ring

theorem constantCoeff_Δ_tatePowerSeries :
    PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
  rw [Δ_tatePowerSeries_eq]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
    constantCoeff_tateA4, constantCoeff_tateA6]
  ring

theorem coeff_one_Δ_tatePowerSeries : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  rw [Δ_tatePowerSeries_eq]
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
    coeff_one_tateA6]
  norm_num

theorem coeff_two_Δ_tatePowerSeries : PowerSeries.coeff 2 tatePowerSeries.Δ = -24 := by
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hmul2 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 2 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have h421 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have h422 : PowerSeries.coeff 2 (tateA4 ^ 2) = 25 := by
    rw [pow_two, hmul2, coeff_zero_tateA4, coeff_one_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 2 (tateA6 ^ 2) = 1 := by
    rw [pow_two, hmul2, coeff_zero_tateA6, coeff_one_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 2 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul2, h420, h421, h422,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 2 (tateA4 * tateA6) = 5 := by
    rw [hmul2, coeff_zero_tateA4, coeff_zero_tateA6, coeff_one_tateA4, coeff_one_tateA6]
    norm_num
  rw [Δ_tatePowerSeries_eq]
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, h422, hsq6, hcb4, hprod,
    coeff_two_tateA6]
  norm_num

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

theorem coeff_one_c₄_tatePowerSeries : PowerSeries.coeff 1 tatePowerSeries.c₄ = 240 := by
  rw [c₄_tatePowerSeries_eq_one_sub, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    coeff_one_tateA4]
  norm_num

theorem coeff_two_c₄_tatePowerSeries : PowerSeries.coeff 2 tatePowerSeries.c₄ = 2160 := by
  rw [c₄_tatePowerSeries_eq_one_sub, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    coeff_two_tateA4]
  norm_num

theorem coeff_one_c₆_tatePowerSeries : PowerSeries.coeff 1 tatePowerSeries.c₆ = 504 := by
  rw [c₆_tatePowerSeries_eq, map_sub, map_add, map_neg, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_one_tateA4, coeff_one_tateA6]
  norm_num

theorem coeff_two_c₆_tatePowerSeries : PowerSeries.coeff 2 tatePowerSeries.c₆ = 16632 := by
  rw [c₆_tatePowerSeries_eq, map_sub, map_add, map_neg, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_two_tateA4, coeff_two_tateA6]
  norm_num

theorem isUnit_Δ_tateLaurent (K : Type*) [CommRing K] : IsUnit (tateLaurent K).Δ :=
  (tateLaurent K).isUnit_Δ

private theorem map_coeffMap_tateLaurent (K : Type*) [CommRing K] (K' : Type*) [CommRing K']
    (f : K →+* K') : (tateLaurent K).map (coeffMap f) = tateLaurent K' := by
  have hcomp : (coeffMap f).comp (laurentOfInt K) = laurentOfInt K' := by
    refine RingHom.ext fun g => ?_
    rw [RingHom.comp_apply]
    ext k
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [coeffMap_coeff, laurentOfInt_apply, laurentOfInt_apply,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map, PowerSeries.coeff_map, ← RingHom.comp_apply,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]
    · rw [coeffMap_coeff, laurentOfInt_apply, laurentOfInt_apply,
        ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  simp only [tateLaurent]
  rw [WeierstrassCurve.map_map, hcomp]

theorem tateLaurent_eq_map_coeffEmb (L : Type*) [Field L] [Algebra ℚ L] :
    tateLaurent L = (tateLaurent ℚ).map (coeffEmb L) :=
  (map_coeffMap_tateLaurent ℚ L (algebraMap ℚ L)).symm

theorem map_coeffMap_algEquiv_tateLaurent (L : Type*) [Field L] [Algebra ℚ L]
    (σ : L ≃ₐ[ℚ] L) : (tateLaurent L).map (coeffMap (σ : L →+* L)) = tateLaurent L :=
  map_coeffMap_tateLaurent L L (σ : L →+* L)

end ModularCurve

end

namespace ModularCurve
p2m_export "ModularCurve" "tateB twelve_mul_tateB tateA4 tateA6 eisenstein6 coeff_tateA4 coeff_tateA6 coeff_zero_tateA4 coeff_zero_tateA6 constantCoeff_tateA4 constantCoeff_tateA6 coeff_one_tateA4 coeff_one_tateA6 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ tatePowerSeries_a₆ laurentOfInt laurentOfInt_apply tateLaurent eisenstein4 ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffEmb"
p2m_open "ModularCurve"

private theorem c4_tatePowerSeries : tatePowerSeries.c₄ = eisenstein4 :=
  c₄_tatePowerSeries

private theorem c6_tatePowerSeries : tatePowerSeries.c₆ = -eisenstein6 :=
  c₆_tatePowerSeries

private theorem constantCoeff_Delta_tatePowerSeries :
    PowerSeries.constantCoeff tatePowerSeries.Δ = 0 :=
  constantCoeff_Δ_tatePowerSeries

private theorem coeff_one_Delta_tatePowerSeries : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 :=
  coeff_one_Δ_tatePowerSeries

private theorem isUnit_Delta_tateLaurent (K : Type*) [CommRing K] : IsUnit (tateLaurent K).Δ :=
  isUnit_Δ_tateLaurent K

end ModularCurve

open PowerSeries HahnSeries _root_.ModularCurve _root_.P2MW.S_ModularCurve_map_coeffMap_tateLaurent.ModularCurve in

theorem solution (K : Type*) [CommRing K] (K' : Type*) [CommRing K']
    (f : K →+* K') : (tateLaurent K).map (coeffMap f) = tateLaurent K' :=
  ModularCurve.map_coeffMap_tateLaurent K K' f

#print axioms solution

end S_ModularCurve_map_coeffMap_tateLaurent
end P2MW
export P2MW.S_ModularCurve_map_coeffMap_tateLaurent (solution)
