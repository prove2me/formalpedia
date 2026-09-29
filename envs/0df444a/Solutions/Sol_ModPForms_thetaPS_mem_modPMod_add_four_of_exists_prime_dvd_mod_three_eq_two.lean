-- Prove2me | solution 1 for ModPForms.thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/81f4819c-789e-50f8-86e2-621d9de0bd71

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_SwdAlgebra
import Theorems.Thm_ModPForms_smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two
import Theorems.Thm_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
import Theorems.Thm_ModPForms_modPMod_le_modPMod_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

namespace SwdAlgebra
p2m_export "SwdAlgebra" "qP"
p2m_open "SwdAlgebra"

p2m_open "PowerSeries P2MW.S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two.PowerSeries"

theorem coeff_qP (F : Type) [Field F] (n : ℕ) :
    coeff n (qP F) = if n = 0 then (1 : F) else ((-24 * ∑ d ∈ n.divisors, (d : ℤ) : ℤ) : F) := by
  simp only [qP, coeff_map, coeff_mk, eq_intCast]
  split_ifs <;> simp

theorem qP_eq_one_of_charP_three (F : Type) [Field F] [CharP F 3] : qP F = 1 := by
  ext n
  rw [coeff_qP, coeff_one]
  split_ifs with h
  · rfl
  · have h24 : ((24 : ℤ) : F) = 0 := by
      have : ((24 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 3 24).mpr (by norm_num)
      exact_mod_cast this
    push_cast
    rw [show (24 : F) = ((24 : ℤ) : F) by push_cast; rfl, h24]
    ring

end SwdAlgebra

namespace PowerSeries
p2m_export "PowerSeries" "subst coeff_mk coeff_C coeff_one coeff_smul coeff_mul coeff_map ext C coeff heckeV coeff_heckeV"
p2m_open "PowerSeries"

theorem heckeV_one {R : Type} [CommRing R] (ℓ : ℕ) (hℓ : ℓ ≠ 0) : heckeV ℓ (1 : PowerSeries R) = 1 := by
  ext n
  simp only [coeff_heckeV, coeff_one]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    split_ifs with hdvd h0
    · exfalso
      obtain ⟨m, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hℓ)] at h0
      exact hn (by rw [h0, mul_zero])
    · rfl
    · rfl

end PowerSeries

namespace ModPForms
p2m_export "ModPForms" "modPMod thetaPS smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two natCast_smul_heckeV_qP_sub_qP_mem_modPMod modPMod_le_modPMod_of_dvd"
p2m_open "ModPForms"

p2m_open "PowerSeries P2MW.S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two.PowerSeries"

theorem one_mem_modPMod_two_of_charP_three (N' : ℕ) [NeZero N']
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2) (F : Type) [Field F] [CharP F 3] :
    (1 : PowerSeries F) ∈ modPMod N' 2 F := by
  obtain ⟨q, hq, hqN, hq3⟩ := hε
  haveI : Fact q.Prime := ⟨hq⟩
  have hmem := ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod q F
  have hqF : (q : F) = 2 := by
    have h : (q : F) = ((2 : ℕ) : F) := (CharP.natCast_eq_natCast F 3).mpr (by
      show q % 3 = 2 % 3
      rw [hq3])
    rw [h, Nat.cast_ofNat]
  rw [SwdAlgebra.qP_eq_one_of_charP_three, PowerSeries.heckeV_one q hq.ne_zero, hqF] at hmem
  have h1 : (2 : F) • (1 : PowerSeries F) - 1 = 1 := by
    rw [two_smul]; abel
  rw [h1] at hmem
  exact ModPForms.modPMod_le_modPMod_of_dvd q N' hqN 2 F hmem

variable {F : Type} [Field F]

theorem coeff_thetaPS (φ : PowerSeries F) (n : ℕ) : coeff n (thetaPS φ) = (n : F) * coeff n φ := by
  simp only [thetaPS, coeff_mk]

@[scoped simp] theorem thetaPS_zero : thetaPS (0 : PowerSeries F) = 0 := by
  ext n; simp [coeff_thetaPS]

theorem thetaPS_add (φ ψ : PowerSeries F) : thetaPS (φ + ψ) = thetaPS φ + thetaPS ψ := by
  ext n; simp only [coeff_thetaPS, map_add, mul_add]

theorem thetaPS_smul (c : F) (φ : PowerSeries F) : thetaPS (c • φ) = c • thetaPS φ := by
  ext n; simp only [coeff_thetaPS, coeff_smul, smul_eq_mul]; ring

theorem thetaPS_neg (φ : PowerSeries F) : thetaPS (-φ) = -thetaPS φ := by
  rw [← neg_one_smul F φ, thetaPS_smul, neg_one_smul]

theorem thetaPS_sub (φ ψ : PowerSeries F) : thetaPS (φ - ψ) = thetaPS φ - thetaPS ψ := by
  rw [sub_eq_add_neg, thetaPS_add, thetaPS_neg, ← sub_eq_add_neg]

@[scoped simp] theorem thetaPS_one : thetaPS (1 : PowerSeries F) = 0 := by
  ext n
  rw [coeff_thetaPS, coeff_one, map_zero]
  split_ifs with h
  · subst h; simp
  · simp

@[scoped simp] theorem thetaPS_C (c : F) : thetaPS (C c) = 0 := by
  ext n
  rw [coeff_thetaPS, coeff_C, map_zero]
  split_ifs with h
  · subst h; simp
  · simp

noncomputable def thetaPSₗ : PowerSeries F →ₗ[F] PowerSeries F where
  toFun := thetaPS
  map_add' := thetaPS_add
  map_smul' := thetaPS_smul

@[scoped simp] theorem thetaPSₗ_apply (φ : PowerSeries F) : thetaPSₗ φ = thetaPS φ := rfl

theorem thetaPS_sum {ι : Type} (s : Finset ι) (φ : ι → PowerSeries F) :
    thetaPS (∑ i ∈ s, φ i) = ∑ i ∈ s, thetaPS (φ i) := by
  simpa only [thetaPSₗ_apply] using map_sum (thetaPSₗ (F := F)) φ s

theorem thetaPS_mul (φ ψ : PowerSeries F) : thetaPS (φ * ψ) = thetaPS φ * ψ + φ * thetaPS ψ := by
  ext n
  rw [map_add, coeff_thetaPS, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [coeff_thetaPS, coeff_thetaPS]
  have hx' : (x.1 : F) + x.2 = n := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have := congrArg (Nat.cast (R := F)) hx
    push_cast at this
    exact this
  rw [← hx']
  ring

end ModPForms
p2m_reactivate "P2MW.S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two.ModPForms"

p2m_open "ModPForms P2MW.S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two.ModPForms"

theorem solution (N' : ℕ) [NeZero N']
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2) (k : ℤ) (F : Type) [Field F] [CharP F 3]
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) :
    thetaPS φ ∈ modPMod N' (k + 4) F := by
  have h1 : (1 : PowerSeries F) ∈ modPMod N' 2 F := ModPForms.one_mem_modPMod_two_of_charP_three N' hε F
  have hrc := ModPForms.smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two N' k 2 F φ 1 hφ h1
  have h2 : ((2 : ℤ) : F) = -1 := by
    have : ((3 : ℕ) : F) = 0 := CharP.cast_eq_zero F 3
    push_cast at this ⊢
    linear_combination this
  rw [ModPForms.thetaPS_one, mul_zero, smul_zero, zero_sub, mul_one, h2, neg_one_smul, neg_neg] at hrc
  convert hrc using 2
  ring

end S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModPForms_thetaPS_mem_modPMod_add_four_of_exists_prime_dvd_mod_three_eq_two (solution)
