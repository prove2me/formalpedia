-- Prove2me | solution 1 for ModularCurve.FullLevel.xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bb173b35-0486-5831-ad10-6273cdfa32cb

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

namespace LevelHFieldQ2

open scoped MatrixGroups
open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

theorem units_zmod_two (u : (ZMod 2)ˣ) : u = 1 := by
  revert u; decide

theorem levelH_two (M' : ℕ) : levelH 2 M' = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro u
  rw [mem_levelH_iff]
  exact units_zmod_two _

theorem gamma0_le_of_dvd {M N : ℕ} (h : M ∣ N) : Gamma0 N ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hA
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (Int.natCast_dvd_natCast.mpr h).trans ⟨c, hc⟩

theorem qExpFunctionFieldC_gamma0_sq_mul_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    qExpFunctionFieldC (ResidueField A) (Gamma0 (q ^ 2 * M')) = modularFunctionFieldC (ResidueField A) M' := by
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  have h1 : Gamma0 (q ^ 2 * M') = CohCarrier.GammaH M' ⊤ ⊓ Gamma0 (M' * q ^ 2) := by
    rw [CohCarrier.GammaH_top, Nat.mul_comm M' (q ^ 2)]
    exact (inf_eq_right.mpr (gamma0_le_of_dvd (Dvd.intro_left (q ^ 2) rfl))).symm
  have h2 : qExpFunctionFieldC (ResidueField A) (Gamma0 (q ^ 2 * M')) =
      xHTopFunctionFieldC (ResidueField A) M' ⊤ (M' * q ^ 2) := by
    rw [xHTopFunctionFieldC, h1]
  rw [h2, xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd M' ⊤ hqM' 2 A hA,
    xHFunctionFieldC_top]
  exact qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd (ResidueField A) M' q hqM'

end LevelHFieldQ2

open ModularCurve ModularCurve.FullLevel IsLocalRing LevelHFieldQ2

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') =
      modularFunctionFieldC (ResidueField A) M' := by
  rw [← qExpFunctionFieldC_gamma0_sq_mul_eq q M' hqM' A hA]
  subst hq2
  rw [levelH_two, xHFunctionFieldC_top]

end S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two (solution)
