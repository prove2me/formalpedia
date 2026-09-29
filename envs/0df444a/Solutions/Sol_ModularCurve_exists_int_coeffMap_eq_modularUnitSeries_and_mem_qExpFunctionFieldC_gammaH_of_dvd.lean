-- Prove2me | solution 1 for ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1aea8b73-f10c-5deb-ac14-e193f7d29047

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

namespace OggUnitPen14

theorem coeffMap_ofPowerSeries {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (x : PowerSeries K) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ K x) = HahnSeries.ofPowerSeries ℤ K' (x.map f) := by
  ext i
  rw [coeffMap_coeff]
  change f (((x : PowerSeries K) : LaurentSeries K).coeff i) = ((x.map f : PowerSeries K') : LaurentSeries K').coeff i
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

noncomputable def Dint : LaurentSeries ℤ := HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit

noncomputable def DpInv (p : ℕ) [NeZero p] : LaurentSeries ℤ :=
  HahnSeries.single (-(p : ℤ)) 1 * qExpand ℤ p (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)

theorem qExpand_Dint_mul_DpInv (p : ℕ) [NeZero p] : qExpand ℤ p Dint * DpInv p = 1 := by
  rw [Dint, DpInv, map_mul, qExpand_single, mul_one, mul_mul_mul_comm, HahnSeries.single_mul_single,
    add_neg_cancel, one_mul, ← map_mul, ← map_mul, dedekindEtaUnit_mul_inv, RingHom.map_one, RingHom.map_one, mul_one]
  rfl

theorem coeffMap_Dint : coeffMap (Int.castRingHom ℚ) Dint = deltaSeries := by
  rw [Dint, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  rfl

theorem coeffMap_DpInv (p : ℕ) [NeZero p] : coeffMap (Int.castRingHom ℚ) (DpInv p) = (deltaSeriesN p)⁻¹ := by
  have h : coeffMap (Int.castRingHom ℚ) (qExpand ℤ p Dint) * coeffMap (Int.castRingHom ℚ) (DpInv p) = 1 := by
    rw [← map_mul, qExpand_Dint_mul_DpInv, map_one]
  rw [coeffMap_qExpand, coeffMap_Dint] at h
  exact (eq_inv_of_mul_eq_one_right h)

noncomputable def xInt (p : ℕ) [NeZero p] : LaurentSeries ℤ := Dint * DpInv p

theorem coeffMap_xInt (p : ℕ) [NeZero p] : coeffMap (Int.castRingHom ℚ) (xInt p) = modularUnitSeries p := by
  rw [xInt, map_mul, coeffMap_Dint, coeffMap_DpInv]
  rfl

end OggUnitPen14

open OggUnitPen14 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∃ x : LaurentSeries ℤ,
        coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
        x.coeff (1 - (p : ℤ)) = 1 ∧ ∀ n : ℤ, n < 1 - (p : ℤ) → x.coeff n = 0) ∧
      modularUnitSeries p ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) ∧
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularUnitSeries p) ∧
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularUnitSeries p)⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨⟨xInt p, coeffMap_xInt p, ?_, ?_⟩, ?_, ModularCurve.isIntegral_adjoin_jq_modularUnitSeries p,
    ModularCurve.isIntegral_adjoin_jq_modularUnitSeries_inv p⟩
  ·
    have h := congrArg (fun f : LaurentSeries ℚ => f.coeff (1 - (p : ℤ))) (coeffMap_xInt p)
    simp only [coeffMap_coeff, coeff_modularUnitSeries_self, eq_intCast] at h
    exact_mod_cast h
  · intro n hn
    have h := congrArg (fun f : LaurentSeries ℚ => f.coeff n) (coeffMap_xInt p)
    simp only [coeffMap_coeff, coeff_modularUnitSeries_of_lt p hn, eq_intCast] at h
    exact_mod_cast h
  ·
    have h0 : CohCarrier.GammaH M H ≤ CongruenceSubgroup.Gamma0 p := by
      intro A hA
      have hA0 := CohCarrier.GammaH_le_Gamma0 H hA
      rw [CongruenceSubgroup.Gamma0_mem] at hA0 ⊢
      have := congrArg (ZMod.castHom hpM (ZMod p)) hA0
      rwa [map_intCast, map_zero] at this
    have hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) :=
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p).trans (qExpFunctionFieldC_mono ℚ h0)
    exact hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p)

end S_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
end P2MW
export P2MW.S_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd (solution)
