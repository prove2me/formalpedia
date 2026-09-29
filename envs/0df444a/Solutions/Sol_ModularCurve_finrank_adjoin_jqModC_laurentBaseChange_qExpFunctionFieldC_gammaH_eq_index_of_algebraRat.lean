-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6f17d7fa-622d-5c42-9933-d4c00bc61339

import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups

theorem solution_bridge {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : E) (hx : x ∈ K) :
    Module.finrank ↥(IntermediateField.adjoin F ({⟨x, hx⟩} : Set ↥K)) ↥K =
      IntermediateField.relfinrank (IntermediateField.adjoin F ({x} : Set E)) K := by
  have hmap : (IntermediateField.adjoin F ({⟨x, hx⟩} : Set ↥K)).map K.val =
      IntermediateField.adjoin F ({x} : Set E) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have h : IntermediateField.adjoin F ({⟨x, hx⟩} : Set ↥K) =
      (IntermediateField.adjoin F ({x} : Set E)).comap K.val := by
    rw [← hmap, IntermediateField.comap_map]
  rw [h, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

theorem solution
    (L : Type) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
    (hy : (y : LaurentSeries L) = ModularCurve.jqModC L) :
    Module.finrank
        ↥(IntermediateField.adjoin L
          ({y} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by

  have hjq : ModularCurve.jq ∈ ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) := by
    have h1 : ModularCurve.jqModC ℚ ∈ ModularCurve.modularFunctionFieldC ℚ M := ModularCurve.jqModC_mem ℚ M
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero] at h1
    exact ModularCurve.qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M h1)

  obtain ⟨yv, hyv⟩ := y
  have hyv' : yv = ModularCurve.coeffEmb L ModularCurve.jq := by
    rw [ModularCurve.coeffEmb_jq]; exact hy
  subst hyv'
  refine (solution_bridge _ _ _).trans ?_
  rw [ModularCurve.relfinrank_laurentBaseChange L _ ModularCurve.jq hjq ModularCurve.transcendental_jq]

  have hmem : ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
    ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjq
  have h8 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
    (AlgebraicClosure ℚ) M H ⟨_, hmem⟩ (ModularCurve.coeffEmb_jq (AlgebraicClosure ℚ))
  have h8' := (solution_bridge _ _ _).symm.trans h8
  rw [ModularCurve.relfinrank_laurentBaseChange (AlgebraicClosure ℚ) _ ModularCurve.jq hjq
    ModularCurve.transcendental_jq] at h8'
  exact h8'

end S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat (solution)
