-- Prove2me | solution 1 for ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5074f450-e572-5c7f-8644-5b0e27cea3bb

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpand_two_etaProd_pow_twentyfour
import Theorems.Thm_ModularCurve_qExpand_two_eisenstein4_mul_etaProd_pow_eight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaInt lambdaModC qExpand qExpand_single qExpand_injective eisenstein4 etaProd constantCoeff_etaProd dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jNumQ jq laurentMap laurentMap_single laurentMap_ofPowerSeries laurentMap_qExpand qExpand_two_etaProd_pow_twentyfour qExpand_two_eisenstein4_mul_etaProd_pow_eight"
p2m_open "ModularCurve"
namespace JLambda

theorem ofPowerSeries_etaProd_ne_zero :
    (HahnSeries.ofPowerSeries ℤ ℚ (etaProd.map (Int.castRingHom ℚ))) ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : LaurentSeries ℚ => x.coeff 0) h
  simp only [HahnSeries.coeff_zero] at h0
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd, map_one] at h0
  exact one_ne_zero h0

theorem main :
    qExpand ℚ 2 jq * lambdaModC ℚ ^ 2 * (16 * lambdaModC ℚ - 1) ^ 2
      = (256 * lambdaModC ℚ ^ 2 - 16 * lambdaModC ℚ + 1) ^ 3 := by

  have F1raw := congrArg (laurentMap (Int.castRingHom ℚ)) ModularCurve.qExpand_two_etaProd_pow_twentyfour
  have F2raw := congrArg (laurentMap (Int.castRingHom ℚ)) ModularCurve.qExpand_two_eisenstein4_mul_etaProd_pow_eight
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
  rw [← hP, ← hE, ← hs] at F2raw
  obtain ⟨p2, hp2⟩ : ∃ p2 : LaurentSeries ℚ, p2 = qExpand ℚ 2 P := ⟨_, rfl⟩
  obtain ⟨p4, hp4⟩ : ∃ p4 : LaurentSeries ℚ, p4 = qExpand ℚ 4 P := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : LaurentSeries ℚ, e = qExpand ℚ 2 E := ⟨_, rfl⟩
  rw [← hp2, ← hp4] at F1raw
  rw [← hp2, ← hp4, ← he] at F2raw
  have hs2 : HahnSeries.single (2 : ℤ) (1 : ℚ) = s ^ 2 := by
    rw [hs, pow_two, HahnSeries.single_mul_single, one_mul]
    rfl
  rw [hs2] at F2raw
  obtain ⟨R, hR⟩ : ∃ R : LaurentSeries ℚ, R = P ^ 16 + 16 * s * P ^ 8 * p4 ^ 8 + 256 * s ^ 2 * p4 ^ 16 := ⟨_, rfl⟩
  have F2' : e * p2 ^ 8 = R := by rw [hR]; linear_combination F2raw

  have hP0 : P ≠ 0 := by rw [hP]; exact ofPowerSeries_etaProd_ne_zero
  have hp20 : p2 ≠ 0 := by
    rw [hp2]
    exact fun h => hP0 (qExpand_injective 2 (by rw [h, map_zero]))
  have hs0 : s ≠ 0 := by rw [hs]; exact HahnSeries.single_ne_zero one_ne_zero
  obtain ⟨y, hy⟩ : ∃ y : LaurentSeries ℚ, y = (p2 ^ 8)⁻¹ := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : LaurentSeries ℚ, t = s⁻¹ := ⟨_, rfl⟩
  have hwy : p2 ^ 8 * y = 1 := by rw [hy]; exact mul_inv_cancel₀ (pow_ne_zero 8 hp20)
  have hst : s * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hs0
  have hX : (P ^ 16 * p4 ^ 8 + 16 * s * P ^ 8 * p4 ^ 16) * y ^ 3 = 1 := by
    linear_combination (-(y ^ 3)) * F1raw + ((p2 ^ 8 * y) ^ 2 + p2 ^ 8 * y + 1) * hwy
  have hey : e = R * y := by linear_combination (-e) * hwy + y * F2'

  have hPI : P ^ 24 * I = 1 := by
    rw [hP, hI, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      show etaProd ^ 24 * dedekindEtaUnitInv = 1 from dedekindEtaUnit_mul_inv, map_one, map_one]
  have hIq : qExpand ℚ 2 I = y ^ 3 := by
    have h1 : p2 ^ 24 * qExpand ℚ 2 I = 1 := by
      rw [hp2, ← map_pow, ← map_mul, hPI, map_one]
    calc qExpand ℚ 2 I = (p2 ^ 8 * y) ^ 3 * qExpand ℚ 2 I := by rw [hwy, one_pow, one_mul]
      _ = y ^ 3 * (p2 ^ 24 * qExpand ℚ 2 I) := by ring
      _ = y ^ 3 := by rw [h1, mul_one]

  have hμ : lambdaModC ℚ = s * P ^ 8 * p4 ^ 16 * y ^ 3 := by
    show laurentMap (Int.castRingHom ℚ) lambdaInt = _
    rw [lambdaInt]
    simp only [map_mul, map_pow, laurentMap_qExpand, laurentMap_ofPowerSeries, laurentMap_single, map_one]
    rw [← hP, ← hs, ← hI, ← hp4, hIq]
  have ht2 : HahnSeries.single (-2 : ℤ) (1 : ℚ) = t ^ 2 := by
    have h1 : HahnSeries.single (-1 : ℤ) (1 : ℚ) = t := by
      rw [ht, hs]
      symm
      apply inv_eq_of_mul_eq_one_right
      rw [HahnSeries.single_mul_single, one_mul]
      rfl
    rw [← h1, pow_two, HahnSeries.single_mul_single, one_mul]
    rfl
  have hj : qExpand ℚ 2 jq = t ^ 2 * (R * y) ^ 3 * y ^ 3 := by
    rw [jq, jNumQ, jNum]
    simp only [map_mul, map_pow, qExpand_single]
    rw [show ((2 : ℕ) : ℤ) * (-1 : ℤ) = -2 by norm_num, ht2, ← hE, ← hI, ← he, hIq, hey]
    ring

  have h1 : 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) - 1 = -(P ^ 16 * p4 ^ 8 * y ^ 3) := by
    linear_combination hX
  have h2 : 256 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) ^ 2 - 16 * (s * P ^ 8 * p4 ^ 16 * y ^ 3) + 1 =
      y ^ 6 * P ^ 16 * p4 ^ 16 * R := by
    rw [hR]
    linear_combination (-(P ^ 16 * p4 ^ 8 * y ^ 3 + 1)) * hX
  rw [hj, hμ, h2, h1]
  linear_combination ((s * t + 1) * R ^ 3 * P ^ 48 * p4 ^ 48 * y ^ 18) * hst

end JLambda
end ModularCurve

theorem solution :
    qExpand ℚ 2 jq * lambdaModC ℚ ^ 2 * (16 * lambdaModC ℚ - 1) ^ 2
      = (256 * lambdaModC ℚ ^ 2 - 16 * lambdaModC ℚ + 1) ^ 3 :=
  ModularCurve.JLambda.main

end S_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
end P2MW
export P2MW.S_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq (solution)
