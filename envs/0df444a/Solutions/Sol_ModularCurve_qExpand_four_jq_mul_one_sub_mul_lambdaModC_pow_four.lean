-- Prove2me | solution 1 for ModularCurve.qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ba5dc480-b457-5ae0-b546-5f787bae4f22

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpand_two_etaProd_pow_twentyfour
import Theorems.Thm_ModularCurve_qExpand_four_eisenstein4_mul_etaProd_identity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaInt lambdaModC qExpand qExpand_single qExpand_injective eisenstein4 etaProd constantCoeff_etaProd dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jNumQ jq laurentMap laurentMap_single laurentMap_ofPowerSeries laurentMap_qExpand qExpand_two_etaProd_pow_twentyfour qExpand_four_eisenstein4_mul_etaProd_identity"
p2m_open "ModularCurve"
namespace JFourM

theorem ofPowerSeries_etaProd_ne_zero :
    (HahnSeries.ofPowerSeries ℤ ℚ (etaProd.map (Int.castRingHom ℚ))) ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : LaurentSeries ℚ => x.coeff 0) h
  simp only [HahnSeries.coeff_zero] at h0
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd, map_one] at h0
  exact one_ne_zero h0

set_option maxRecDepth 20000 in
theorem main :
    qExpand ℚ 4 jq * (1 - 16 * lambdaModC ℚ) * lambdaModC ℚ ^ 4
      = (1 - 16 * lambdaModC ℚ + 16 * lambdaModC ℚ ^ 2) ^ 3 := by

  have F1raw := congrArg (laurentMap (Int.castRingHom ℚ)) ModularCurve.qExpand_two_etaProd_pow_twentyfour
  have F2raw := congrArg (laurentMap (Int.castRingHom ℚ)) ModularCurve.qExpand_four_eisenstein4_mul_etaProd_identity
  simp only [map_add, map_mul, map_pow, map_ofNat, laurentMap_qExpand, laurentMap_ofPowerSeries,
    laurentMap_single, map_one] at F1raw F2raw

  obtain ⟨P, hP⟩ : ∃ P : LaurentSeries ℚ,
      P = HahnSeries.ofPowerSeries ℤ ℚ (etaProd.map (Int.castRingHom ℚ)) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : LaurentSeries ℚ,
      E = HahnSeries.ofPowerSeries ℤ ℚ (eisenstein4.map (Int.castRingHom ℚ)) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : LaurentSeries ℚ,
      I = HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ)) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : LaurentSeries ℚ, s = HahnSeries.single (1 : ℤ) (1 : ℚ) := ⟨_, rfl⟩
  rw [← hP, ← hs] at F1raw
  rw [← hP] at F2raw
  rw [← hE] at F2raw
  obtain ⟨p2, hp2⟩ : ∃ p2 : LaurentSeries ℚ, p2 = qExpand ℚ 2 P := ⟨_, rfl⟩
  obtain ⟨p4, hp4⟩ : ∃ p4 : LaurentSeries ℚ, p4 = qExpand ℚ 4 P := ⟨_, rfl⟩
  obtain ⟨e4, he4⟩ : ∃ e4 : LaurentSeries ℚ, e4 = qExpand ℚ 4 E := ⟨_, rfl⟩
  rw [← hp2, ← hp4] at F1raw
  rw [← hp2, ← hp4, ← he4] at F2raw

  have hP0 : P ≠ 0 := by rw [hP]; exact ofPowerSeries_etaProd_ne_zero
  have hp20 : p2 ≠ 0 := by
    rw [hp2]
    exact fun h => hP0 (qExpand_injective 2 (by rw [h, map_zero]))
  have hp40 : p4 ≠ 0 := by
    rw [hp4]
    exact fun h => hP0 (qExpand_injective 4 (by rw [h, map_zero]))
  have hs0 : s ≠ 0 := by rw [hs]; exact HahnSeries.single_ne_zero one_ne_zero
  obtain ⟨y, hy⟩ : ∃ y : LaurentSeries ℚ, y = (p2 ^ 8)⁻¹ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : LaurentSeries ℚ, v = (p4 ^ 8)⁻¹ := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : LaurentSeries ℚ, t = s⁻¹ := ⟨_, rfl⟩
  have hwy : p2 ^ 8 * y = 1 := by rw [hy]; exact mul_inv_cancel₀ (pow_ne_zero 8 hp20)
  have hpv : p4 ^ 8 * v = 1 := by rw [hv]; exact mul_inv_cancel₀ (pow_ne_zero 8 hp40)
  have hst : s * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hs0
  have hX : (P ^ 16 * p4 ^ 8 + 16 * s * P ^ 8 * p4 ^ 16) * y ^ 3 = 1 := by
    linear_combination (-(y ^ 3)) * F1raw + ((p2 ^ 8 * y) ^ 2 + p2 ^ 8 * y + 1) * hwy

  have hPI : P ^ 24 * I = 1 := by
    rw [hP, hI, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      show etaProd ^ 24 * dedekindEtaUnitInv = 1 from dedekindEtaUnit_mul_inv, map_one, map_one]
  have hIq2 : qExpand ℚ 2 I = y ^ 3 := by
    have h1 : p2 ^ 24 * qExpand ℚ 2 I = 1 := by
      rw [hp2, ← map_pow, ← map_mul, hPI, map_one]
    calc qExpand ℚ 2 I = (p2 ^ 8 * y) ^ 3 * qExpand ℚ 2 I := by rw [hwy, one_pow, one_mul]
      _ = y ^ 3 * (p2 ^ 24 * qExpand ℚ 2 I) := by ring
      _ = y ^ 3 := by rw [h1, mul_one]
  have hIq4 : qExpand ℚ 4 I = v ^ 3 := by
    have h1 : p4 ^ 24 * qExpand ℚ 4 I = 1 := by
      rw [hp4, ← map_pow, ← map_mul, hPI, map_one]
    calc qExpand ℚ 4 I = (p4 ^ 8 * v) ^ 3 * qExpand ℚ 4 I := by rw [hpv, one_pow, one_mul]
      _ = v ^ 3 * (p4 ^ 24 * qExpand ℚ 4 I) := by ring
      _ = v ^ 3 := by rw [h1, mul_one]

  have hμ : lambdaModC ℚ = s * P ^ 8 * p4 ^ 16 * y ^ 3 := by
    show laurentMap (Int.castRingHom ℚ) lambdaInt = _
    rw [lambdaInt]
    simp only [map_mul, map_pow, laurentMap_qExpand, laurentMap_ofPowerSeries, laurentMap_single, map_one]
    rw [← hP, ← hs, ← hI, ← hp4, hIq2]
  have ht1 : HahnSeries.single (-1 : ℤ) (1 : ℚ) = t := by
    rw [ht, hs]
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [HahnSeries.single_mul_single, one_mul]
    rfl
  have ht2 : HahnSeries.single (-2 : ℤ) (1 : ℚ) = t ^ 2 := by
    rw [← ht1, pow_two, HahnSeries.single_mul_single, one_mul]
    rfl
  have ht4 : HahnSeries.single (-4 : ℤ) (1 : ℚ) = t ^ 4 := by
    rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring, ← ht2, HahnSeries.single_mul_single, one_mul]
    rfl
  have hj : qExpand ℚ 4 jq = t ^ 4 * e4 ^ 3 * v ^ 3 := by
    rw [jq, jNumQ, jNum]
    simp only [map_mul, map_pow, qExpand_single]
    rw [show ((4 : ℕ) : ℤ) * (-1 : ℤ) = -4 by norm_num, ht4, ← hE, ← hI, ← he4, hIq4]
    ring

  have h1 : 1 - 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) = P ^ 16 * p4 ^ 8 * y ^ 3 := by
    linear_combination (-1 : LaurentSeries ℚ) * hX
  have h16 : (16 : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℚ)) 16, HahnSeries.C_apply]
    exact HahnSeries.single_ne_zero (by norm_num)
  have h2x : 16 * (1 - 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) + 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) ^ 2) =
      16 * (e4 * P ^ 16 * p4 ^ 16 * y ^ 5) := by
    linear_combination (-(y ^ 6)) * F2raw
      + (y ^ 6 * (15 * p2 ^ 24 + P ^ 16 * p4 ^ 8 - 16 * (s * P ^ 8 * p4 ^ 16))) * F1raw
      - 16 * ((1 + y * p2 ^ 8 + (y * p2 ^ 8) ^ 2 + (y * p2 ^ 8) ^ 3 + (y * p2 ^ 8) ^ 4 + (y * p2 ^ 8) ^ 5)
          - 16 * (s * P ^ 8 * p4 ^ 16) * y ^ 3 * (1 + y * p2 ^ 8 + (y * p2 ^ 8) ^ 2)
          - e4 * P ^ 16 * p4 ^ 16 * y ^ 5) * hwy
  have h2 : 1 - 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) + 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) ^ 2 =
      e4 * P ^ 16 * p4 ^ 16 * y ^ 5 := mul_left_cancel₀ h16 h2x
  rw [hj, hμ, h2, h1]
  linear_combination (e4 ^ 3 * P ^ 48 * y ^ 15 * p4 ^ 48) *
    (((s * t) ^ 3 + (s * t) ^ 2 + s * t + 1) * (p4 ^ 8 * v) ^ 3 * hst + ((p4 ^ 8 * v) ^ 2 + p4 ^ 8 * v + 1) * hpv)

end JFourM
end ModularCurve

theorem solution :
    qExpand ℚ 4 jq * (1 - 16 * lambdaModC ℚ) * lambdaModC ℚ ^ 4
      = (1 - 16 * lambdaModC ℚ + 16 * lambdaModC ℚ ^ 2) ^ 3 :=
  ModularCurve.JFourM.main

end S_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four
end P2MW
export P2MW.S_ModularCurve_qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four (solution)
