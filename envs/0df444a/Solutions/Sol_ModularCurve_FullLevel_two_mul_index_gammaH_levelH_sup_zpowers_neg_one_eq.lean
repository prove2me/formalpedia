-- Prove2me | solution 1 for ModularCurve.FullLevel.two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/568cd27d-4c87-5234-a02c-bc446efcef47

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi Gamma0_index dedekindPsi_mul_of_coprime dedekindPsi_prime_pow"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "dvd_sq_mul levelH mem_levelH_iff"
namespace IdxH
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem mem_zpowers_neg_one {z : SL(2, ℤ)} (hz : z ∈ Subgroup.zpowers (-1 : SL(2, ℤ))) : z = 1 ∨ z = -1 := by
  rw [Subgroup.zpowers_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx => right; simpa using hx
  | one => left; rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · left; exact one_mul 1
    · right; exact one_mul _
    · right; exact mul_one _
    · left; rw [neg_mul_neg, one_mul]
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · left; exact inv_one
    · right; exact inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, one_mul])

scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases mem_zpowers_neg_one hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg, mul_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem two_mul_index_sup_of_neg_one_not_mem (K : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∉ K) :
    2 * (K ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = K.index := by
  set Z := Subgroup.zpowers (-1 : SL(2, ℤ))
  have hrel : K.relIndex (K ⊔ Z) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), fun b hb => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rcases mem_zpowers_neg_one hz with rfl | rfl
    · rw [mul_one, xor_def]
      right
      refine ⟨hy, fun h => hneg ?_⟩
      have : y⁻¹ * (y * -1) ∈ K := K.mul_mem (K.inv_mem hy) h
      rwa [inv_mul_cancel_left] at this
    · rw [xor_def]
      left
      refine ⟨by rw [mul_assoc, neg_mul_neg, one_mul, mul_one]; exact hy, fun h => hneg ?_⟩
      have : y⁻¹ * (y * -1) ∈ K := K.mul_mem (K.inv_mem hy) h
      rwa [inv_mul_cancel_left] at this
  rw [← Subgroup.relIndex_mul_index (le_sup_left : K ≤ K ⊔ Z), hrel]

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

theorem neg_one_not_mem (hq : 3 ≤ q) :
    (-1 : SL(2, ℤ)) ∉ CohCarrier.GammaH (q ^ 2 * M') (levelH q M') := by
  intro h
  rw [CohCarrier.mem_GammaH_iff] at h
  obtain ⟨h0, hH⟩ := h
  rw [mem_levelH_iff] at hH
  have hd : (ZMod.cast (-1 : ZMod (q ^ 2 * M')) : ZMod q) = 1 := by
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simpa [ZMod.unitsMap, CohCarrier.val_gamma0Units, CongruenceSubgroup.Gamma0Map, ZMod.castHom_apply] using this
  rw [ZMod.cast_neg (dvd_sq_mul q M'), ZMod.cast_one (dvd_sq_mul q M')] at hd
  have h2 : ((2 : ℕ) : ZMod q) = 0 := by
    have : (1 : ZMod q) + 1 = 0 := by
      nth_rewrite 1 [← hd]; exact neg_add_cancel 1
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem index_levelH : (levelH q M').index = q - 1 := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  unfold levelH
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (dvd_sq_mul q M')),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]

theorem main (hq : 3 ≤ q) (hqM' : ¬ q ∣ M') :
    2 * (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      q * (q ^ 2 - 1) * dedekindPsi M' := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  have hp : q.Prime := Fact.out
  rw [two_mul_index_sup_of_neg_one_not_mem _ (neg_one_not_mem q M' hq),
    CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index, index_levelH,
    ModularCurve.dedekindPsi_mul_of_coprime _ _ (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hqM')),
    ModularCurve.dedekindPsi_prime_pow q 2 hp two_ne_zero]
  have h1 : 1 ≤ q := hp.one_le
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hp.pos
  zify [h1, h2]
  ring

end ModularCurve.FullLevel.IdxH
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve.FullLevel.IdxH"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq.ModularCurve"

open ModularCurve.FullLevel.IdxH in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    2 * (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      q * (q ^ 2 - 1) * dedekindPsi M' :=
  ModularCurve.FullLevel.IdxH.main q M' hq hqM'

end S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq (solution)
