-- Prove2me | solution 1 for ModularCurve.smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/69720717-20c8-516f-abeb-7ee8d61301dc

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring
import Theorems.Thm_AlgebraicCurve_ordDifferential_map_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

p2m_open "ModularCurve~coeffEmb_injective~coeffMap_ofPowerSeries P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.ModularCurve AlgebraicCurve KaehlerDifferential HahnSeries IntermediateField CongruenceSubgroup"
open scoped MatrixGroups TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC qExpFunctionFieldC_mono x1FunctionFieldBar ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff laurentBaseChange jqModC thetaL thetaL_apply qExpansionDiffAlong qEuler qEuler_coeff diffQExp diffQExp_D exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed laurentBaseChange_adjoin qExpansionDiffAlong_D qExpansionDiffAlong_smul coeff_jqModC_neg_one"
namespace OmegaGammaHCharZeroProof
p2m_open "ModularCurve~coeffEmb_injective~coeffMap_ofPowerSeries"

local notation "ℚbar" => AlgebraicClosure ℚ

section QExp

variable {L : Type*} [Field L] (E : IntermediateField L (LaurentSeries L))

local notation "qE" => qExpansionDiffAlong (IntermediateField.val E)

theorem qE_add (η η' : Ω[E⁄L]) : qE (η + η') = qE η + qE η' := map_add _ _ _

theorem qE_zero : qE (0 : Ω[E⁄L]) = 0 := map_zero _

theorem qE_D (x : E) : qE (D L E x) = thetaL L (x : LaurentSeries L) := qExpansionDiffAlong_D _ x

theorem qE_smul (g : E) (η : Ω[E⁄L]) : qE (g • η) = (g : LaurentSeries L) * qE η :=
  qExpansionDiffAlong_smul _ g η

theorem qE_smul_D (x y : E) : qE (x • D L E y) = (x : LaurentSeries L) * thetaL L (y : LaurentSeries L) := by
  rw [qE_smul, qE_D]

theorem thetaL_eq_qEuler (x : LaurentSeries L) : thetaL L x = qEuler L x := by
  ext n
  rw [thetaL_apply, coeff_single_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, qEuler_coeff, Nat.cast_one, sub_add_cancel,
    Ring.choose_one_right, one_mul, zsmul_eq_mul]

theorem diffQExp_add (η η' : Ω[E⁄L]) : diffQExp E (η + η') = diffQExp E η + diffQExp E η' :=
  map_add _ _ _

theorem diffQExp_zero : diffQExp E (0 : Ω[E⁄L]) = 0 := map_zero _

theorem qE_eq_diffQExp (η : Ω[E⁄L]) : qE η = diffQExp E η := by
  have hη : η ∈ Submodule.span E (Set.range (D L E)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hη using Submodule.span_induction with
  | mem ω hω =>
      obtain ⟨x, rfl⟩ := hω
      rw [qE_D, diffQExp_D, thetaL_eq_qEuler]
  | zero => rw [qE_zero, diffQExp_zero]
  | add ω ω' _ _ h h' => rw [qE_add, diffQExp_add, h, h']
  | smul g ω _ h =>
      rw [qE_smul, map_smul, h]
      rfl

theorem thetaL_jqModC_ne_zero : thetaL L (jqModC L) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries L => x.coeff (-1 : ℤ)) h
  beta_reduce at h1
  rw [thetaL_apply, coeff_single_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Nat.cast_one, show (-1 : ℤ) - 1 + 1 = -1 by norm_num, Ring.choose_one_right,
    ModularCurve.coeff_jqModC_neg_one] at h1
  simp at h1

theorem qE_injective (j : E) (hj : (j : LaurentSeries L) = jqModC L) (htr : Transcendental L j)
    [Algebra.IsSeparable (IntermediateField.adjoin L ({j} : Set E)) E] :
    Function.Injective qE := by
  intro ω₁ ω₂ hω
  obtain ⟨c₁, hc₁, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental L j htr ω₁
  obtain ⟨c₂, hc₂, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental L j htr ω₂
  rw [hc₁, hc₂, qE_smul_D, qE_smul_D, hj] at hω
  have h := mul_right_cancel₀ (thetaL_jqModC_ne_zero (L := L)) hω
  rw [hc₁, hc₂, show c₁ = c₂ from Subtype.ext h]

end QExp

section Fields

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem curve_structure (K : Type*) [Field K] [IsAlgClosed K] (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    (∃ x : qExpFunctionFieldC K Γ, (x : LaurentSeries K) = jqModC K ∧ Transcendental K x ∧
        FiniteDimensional (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
          (qExpFunctionFieldC K Γ)) ∧
      IsCurveOver K ↥(qExpFunctionFieldC K Γ) ∧ Algebra.EssFiniteType K ↥(qExpFunctionFieldC K Γ) := by
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨x, hxj, htr, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  exact ⟨⟨x, hxj, htr, hfd⟩, isCurveOver_of_transcendental_of_perfectField htr hfd,
    essFiniteType_of_transcendental_of_finiteDimensional htr hfd⟩

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext i
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hi
  · exact map_zero φ
  · rw [PowerSeries.coeff_map]

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  rw [coeffEmb, intSeriesC, coeffMap_ofPowerSeries, intSeriesC]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffEmb_injective : Function.Injective (coeffEmb L) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ L).injective h1

theorem image_intFormRatiosC : coeffEmb L '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  ext z
  constructor
  · rintro ⟨_, ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    have hgL : intSeriesC L pg ≠ 0 := by
      rw [← coeffEmb_intSeriesC L]
      exact (map_ne_zero_iff _ (coeffEmb_injective L)).mpr hg0
    refine ⟨κ, f, g, pf, pg, hf, hg, hgL, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hgQ : intSeriesC ℚ pg ≠ 0 := by
      intro h
      apply hg0
      rw [← coeffEmb_intSeriesC L, h, map_zero]
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨κ, f, g, pf, pg, hf, hg, hgQ, rfl⟩, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

theorem laurentBaseChange_qExpFunctionFieldC :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC L Γ := by
  rw [qExpFunctionFieldC, laurentBaseChange_adjoin, image_intFormRatiosC]
  rfl

end BaseChange

theorem x1FunctionFieldBar_eq (M : ℕ) :
    x1FunctionFieldBar M = qExpFunctionFieldC ℚbar (Gamma1 M) :=
  laurentBaseChange_qExpFunctionFieldC ℚbar (Gamma1 M)

variable {M : ℕ} {Γ : Subgroup SL(2, ℤ)}

abbrev FH (Γ : Subgroup SL(2, ℤ)) : IntermediateField ℚbar (LaurentSeries ℚbar) := qExpFunctionFieldC ℚbar Γ

abbrev F1 (M : ℕ) : IntermediateField ℚbar (LaurentSeries ℚbar) := qExpFunctionFieldC ℚbar (Gamma1 M)

theorem FH_le_F1 (hΓ₁ : Gamma1 M ≤ Γ) : FH Γ ≤ F1 M := qExpFunctionFieldC_mono ℚbar hΓ₁

theorem T_mem (hΓ₁ : Gamma1 M ≤ Γ) : ModularGroup.T ∈ Γ := hΓ₁ (T_mem_Gamma1 M)

theorem finiteIndex [NeZero M] (hΓ₁ : Gamma1 M ≤ Γ) : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁

@[reducible] def algIncl (h : FH Γ ≤ F1 M) : Algebra (FH Γ) (F1 M) :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

theorem algebraMap_incl_apply (h : FH Γ ≤ F1 M) (y : FH Γ) :
    letI := algIncl h
    algebraMap (FH Γ) (F1 M) y = IntermediateField.inclusion h y := rfl

theorem coe_algebraMap_incl (h : FH Γ ≤ F1 M) (y : FH Γ) :
    letI := algIncl h
    ((algebraMap (FH Γ) (F1 M) y : F1 M) : LaurentSeries ℚbar) = (y : LaurentSeries ℚbar) := by
  rw [algebraMap_incl_apply]
  exact IntermediateField.coe_inclusion h y

theorem isScalarTower_incl (h : FH Γ ≤ F1 M) :
    letI := algIncl h
    IsScalarTower ℚbar (FH Γ) (F1 M) := by
  letI := algIncl h
  refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
  rw [algebraMap_incl_apply]
  apply Subtype.ext
  rw [IntermediateField.coe_inclusion]
  exact (IntermediateField.coe_algebraMap_apply (S := F1 M) c).trans
    (IntermediateField.coe_algebraMap_apply (S := FH Γ) c).symm

theorem finite_incl (h : FH Γ ≤ F1 M) (j : FH Γ) (x₁ : F1 M)
    (hjx : (j : LaurentSeries ℚbar) = (x₁ : LaurentSeries ℚbar))
    (hfd : FiniteDimensional (IntermediateField.adjoin ℚbar ({x₁} : Set (F1 M))) (F1 M)) :
    letI := algIncl h
    Module.Finite (FH Γ) (F1 M) := by
  letI := algIncl h
  haveI := isScalarTower_incl (M := M) (Γ := Γ) h
  set R := IntermediateField.adjoin ℚbar ({x₁} : Set (F1 M)) with hR

  have hrange : ∀ r : R, ∃ s : FH Γ, algebraMap (FH Γ) (F1 M) s = (r : F1 M) := by
    have hle : R ≤ (IntermediateField.inclusion h).fieldRange := by
      rw [hR, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      refine ⟨j, ?_⟩
      apply Subtype.ext
      change ((IntermediateField.inclusion h j : F1 M) : LaurentSeries ℚbar) = _
      rw [IntermediateField.coe_inclusion]
      exact hjx
    intro r
    obtain ⟨s, hs⟩ := AlgHom.mem_fieldRange.mp (hle r.2)
    exact ⟨s, hs⟩

  obtain ⟨G, hG⟩ := Module.finite_def.mp hfd
  refine Module.finite_def.mpr ⟨G, ?_⟩
  rw [eq_top_iff]
  rintro t -
  have ht : t ∈ Submodule.span R (G : Set (F1 M)) := by rw [hG]; exact Submodule.mem_top
  induction ht using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy =>
      obtain ⟨s, hs⟩ := hrange r
      have : (r • y : F1 M) = s • y := by
        rw [Algebra.smul_def, Algebra.smul_def, hs]
        rfl
      rw [this]
      exact Submodule.smul_mem _ s hy

end Fields

section LevelOne

open ModularForm ModularFormClass
p2m_open "UpperHalfPlane~I"

variable (M : ℕ)

abbrev S2 : Type := CuspForm (Gamma1 M) 2

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

def qCoeffLin (n : ℕ) : S2 M →ₗ[ℂ] ℂ where
  toFun f := qCoeff f n
  map_add' f g := by
    simp only [qCoeff, CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) f g, map_add]
  map_smul' c f := by
    simp only [qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f]
    simp

@[scoped simp] lemma qCoeffLin_apply (n : ℕ) (f : S2 M) : qCoeffLin M n f = qCoeff f n := rfl

variable {M}

def restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ)
    (f : CuspForm Γ k) : (⇑(restrictCusp h f) : ℍ → ℂ) = f := rfl

def red (a : ℕ → ℤ) : LaurentSeries ℚbar :=
  HahnSeries.ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar))

theorem red_coeff_nat (a : ℕ → ℤ) (n : ℕ) : (red a).coeff (n : ℤ) = (a n : ℚbar) := by
  rw [red, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem red_coeff_neg (a : ℕ → ℤ) {n : ℤ} (hn : n < 0) : (red a).coeff n = 0 := by
  rw [red, ModularCurve.ofPowerSeries_coeff_of_neg _ hn]

variable (M) [NeZero M]

local notation "qE1" => qExpansionDiffAlong (IntermediateField.val (qExpFunctionFieldC ℚbar (Gamma1 M)))

abbrev Reg : Submodule ℚbar (Ω[F1 M⁄ℚbar]) := regularDifferentials ℚbar (F1 M)

theorem qE1_injective : Function.Injective qE1 := by
  obtain ⟨⟨x₁, hx₁, htr, hfd⟩, -, -⟩ := curve_structure ℚbar (Gamma1 M) (T_mem_Gamma1 M)
  haveI := hfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin ℚbar ({x₁} : Set (F1 M))) (F1 M) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact qE_injective (F1 M) x₁ hx₁ htr

def qECoeff (n : ℤ) : Ω[F1 M⁄ℚbar] →ₗ[ℚbar] ℚbar :=
  (HahnSeries.coeff.linearMap (Γ := ℤ) (R := ℚbar) (V := ℚbar) n) ∘ₗ qE1

omit [NeZero M] in
theorem qECoeff_apply (n : ℤ) (ω : Ω[F1 M⁄ℚbar]) : qECoeff M n ω = (qE1 ω).coeff n := rfl

def regCoeff (n : ℤ) : ↥(Reg M) →ₗ[ℚbar] ℚbar := (qECoeff M n) ∘ₗ (Reg M).subtype

omit [NeZero M] in
theorem regCoeff_apply (n : ℤ) (ω : ↥(Reg M)) : regCoeff M n ω = (qE1 (ω : Ω[F1 M⁄ℚbar])).coeff n := rfl

omit [NeZero M] in
theorem coeff_qE1_sum_smul {ι : Type*} (s : Finset ι) (d : ι → ℚbar) (ω : ι → ↥(Reg M)) (n : ℤ) :
    (qE1 ((∑ i ∈ s, d i • ω i : ↥(Reg M)) : Ω[F1 M⁄ℚbar])).coeff n =
      ∑ i ∈ s, d i * (qE1 ((ω i : ↥(Reg M)) : Ω[F1 M⁄ℚbar])).coeff n := by
  rw [← regCoeff_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, regCoeff_apply]

theorem exists_reg_F1 (g : S2 M) (a : ℕ → ℤ) (ha : ∀ n : ℕ, qCoeff (⇑g : ℍ → ℂ) n = (a n : ℂ)) :
    ∃ ω₁ ∈ Reg M, qE1 ω₁ = red a := by
  classical
  haveI : Algebra.IsAlgebraic ℚ ℚbar := AlgebraicClosure.isAlgebraic ℚ
  let ι₀ : ℚbar →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := ℚbar) (M := ℂ)).toRingHom
  letI : Algebra ℚbar ℂ := ι₀.toAlgebra

  have key : ∀ E : IntermediateField ℚbar (LaurentSeries ℚbar), E = x1FunctionFieldBar M →
      ∃ e : ℂ ⊗[ℚbar] ↥(regularDifferentials ℚbar E) ≃ₗ[ℂ] S2 M,
        ∀ ω : ↥(regularDifferentials ℚbar E),
          coeffMap ι₀ (diffQExp E (ω : Ω[E⁄ℚbar])) =
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑(e (1 ⊗ₜ ω))) := by
    rintro E rfl
    exact ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm M ι₀
  obtain ⟨e, he⟩ := key (F1 M) (x1FunctionFieldBar_eq M).symm

  let b := Module.Free.chooseBasis ℚbar ↥(Reg M)
  let bC := Algebra.TensorProduct.basis ℂ b
  set t : ℂ ⊗[ℚbar] ↥(Reg M) := e.symm g with htdef
  set c : Module.Free.ChooseBasisIndex ℚbar ↥(Reg M) → ℂ := fun i => bC.repr t i with hcdef
  set s := (bC.repr t).support with hsdef
  have ht : t = ∑ i ∈ s, c i • ((1 : ℂ) ⊗ₜ[ℚbar] (b i)) := by
    conv_lhs => rw [← bC.linearCombination_repr t, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]

  let G : Module.Free.ChooseBasisIndex ℚbar ↥(Reg M) → ℤ → ℚbar :=
    fun i n => (qE1 ((b i : ↥(Reg M)) : Ω[F1 M⁄ℚbar])).coeff n
  have hG : ∀ i n, G i n = (qE1 ((b i : ↥(Reg M)) : Ω[F1 M⁄ℚbar])).coeff n := fun _ _ => rfl
  have hGι : ∀ i (n : ℤ), ι₀ (G i n) =
      (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑(e (1 ⊗ₜ (b i))))).coeff n := by
    intro i n
    have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff n) (he (b i))
    simp only [coeffMap_coeff] at h1
    rw [← h1, hG, qE_eq_diffQExp]
  have hGneg : ∀ i (n : ℤ), n < 0 → G i n = 0 := by
    intro i n hn
    apply ι₀.injective
    rw [hGι, ModularCurve.ofPowerSeries_coeff_of_neg _ hn, map_zero]
  have hGnat : ∀ i (n : ℕ), ι₀ (G i n) = qCoeff (⇑(e (1 ⊗ₜ (b i))) : ℍ → ℂ) n := by
    intro i n
    rw [hGι, HahnSeries.ofPowerSeries_apply_coeff]
    rfl

  have hrel : ∀ n : ℕ, ∑ i ∈ s, c i * ι₀ (G i n) = ι₀ (a n) := by
    intro n
    have h1 : (a n : ℂ) = qCoeffLin M n g := by rw [qCoeffLin_apply, ha]
    rw [map_intCast, h1, ← e.apply_symm_apply g, ← htdef, ht, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearEquiv.map_smul, LinearMap.map_smul, smul_eq_mul, qCoeffLin_apply, hGnat]

  have hind : ∀ d : Module.Free.ChooseBasisIndex ℚbar ↥(Reg M) → ℚbar,
      (∀ n : ℕ, ∑ i ∈ s, d i * G i n = 0) → ∀ i ∈ s, d i = 0 := by
    intro d hd
    have hω : qE1 ((∑ i ∈ s, d i • b i : ↥(Reg M)) : Ω[F1 M⁄ℚbar]) = 0 := by
      ext n
      rw [HahnSeries.coeff_zero, coeff_qE1_sum_smul]
      simp_rw [← hG]
      rcases lt_or_ge n 0 with hn | hn
      · exact Finset.sum_eq_zero fun i _ => by rw [hGneg i n hn, mul_zero]
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        exact hd m
    have hω0 : (∑ i ∈ s, d i • b i : ↥(Reg M)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_zero]
      exact qE1_injective M (hω.trans (map_zero _).symm)
    exact linearIndependent_iff'.mp b.linearIndependent s d hω0

  set W : Submodule ℚbar ℂ := LinearMap.range (Algebra.linearMap ℚbar ℂ) with hWdef
  have hcW : ∀ i ∈ s, c i ∈ W := by
    let B' := Module.Free.chooseBasis ℚbar (ℂ ⧸ W)
    have hcoord : ∀ l, ∀ i ∈ s, B'.repr (W.mkQ (c i)) l = 0 := by
      intro l
      refine hind (fun i => B'.repr (W.mkQ (c i)) l) ?_
      intro n
      let φ : ℂ →ₗ[ℚbar] ℚbar := (B'.coord l) ∘ₗ W.mkQ
      have hφ : ∀ z, φ z = B'.repr (W.mkQ z) l := fun z => rfl
      have h0 : φ (ι₀ (a n)) = 0 := by
        have hmem : ι₀ (a n) ∈ W := ⟨a n, rfl⟩
        rw [hφ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hmem, map_zero,
          Finsupp.zero_apply]
      rw [← hrel n, map_sum] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show c i * ι₀ (G i n) = G i n • c i from by rw [Algebra.smul_def, mul_comm]; rfl,
        LinearMap.map_smul, smul_eq_mul, mul_comm, hφ]
    intro i hi
    have hq : W.mkQ (c i) = 0 := by
      rw [← B'.repr.map_eq_zero_iff]
      ext l
      rw [hcoord l i hi, Finsupp.zero_apply]
    rw [Submodule.mkQ_apply] at hq
    exact (Submodule.Quotient.mk_eq_zero W).mp hq
  choose! c' hc' using fun i (hi : i ∈ s) => LinearMap.mem_range.mp (hcW i hi)

  refine ⟨((∑ i ∈ s, c' i • b i : ↥(Reg M)) : Ω[F1 M⁄ℚbar]), Submodule.coe_mem _, ?_⟩
  ext n
  rw [coeff_qE1_sum_smul]
  simp_rw [← hG]
  rcases lt_or_ge n 0 with hn | hn
  · rw [red_coeff_neg a hn]
    exact Finset.sum_eq_zero fun i _ => by rw [hGneg i n hn, mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [red_coeff_nat]
    refine ι₀.injective ?_
    calc ι₀ (∑ i ∈ s, c' i * G i m) = ∑ i ∈ s, c i * ι₀ (G i m) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i hi => by rw [map_mul, show ι₀ (c' i) = c i from hc' i hi]
      _ = ι₀ (a m) := hrel m

end LevelOne

section Descent

open ModularFormClass

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  set g : v.toValuationSubring := ⟨f, hf⟩ with hg
  change 0 ≤ v.ord (g : F)
  by_cases hg0 : g = 0
  · simp [hg0]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hπ
  have : (g : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem ordDifferential_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] (w : Place K F) [w.DCoordGenerates] {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) : 0 ≤ w.ordDifferential ω := by
  obtain ⟨h, hh, hωh⟩ := hω w
  rw [Place.ordDifferential, w.differentialCoeff_unique hωh]
  exact ord_nonneg_of_mem w hh

variable {M : ℕ} [NeZero M] {Γ : Subgroup SL(2, ℤ)} (hΓ₁ : Gamma1 M ≤ Γ)
  (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (a : ℕ → ℤ)
  (ha : ∀ n : ℕ, qCoeff (⇑f : UpperHalfPlane → ℂ) n = (a n : ℂ))
  (x j : FH Γ) (hj : (j : LaurentSeries ℚbar) = jqModC ℚbar)
  (hx : (x : LaurentSeries ℚbar) * thetaL ℚbar (jqModC ℚbar) =
    HahnSeries.ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)))

include hΓ₁ ha hj hx in
theorem main : x • D ℚbar (FH Γ) j ∈ regularDifferentials ℚbar (FH Γ) := by

  haveI := finiteIndex hΓ₁
  have hT := T_mem hΓ₁
  have hle : FH Γ ≤ F1 M := FH_le_F1 hΓ₁
  letI := algIncl hle
  haveI := isScalarTower_incl (M := M) (Γ := Γ) hle
  haveI : PerfectField ℚbar := IsAlgClosed.perfectField _
  obtain ⟨⟨x₀, -, -, hfd₀⟩, hco₀, hess₀⟩ := curve_structure ℚbar Γ hT
  obtain ⟨⟨x₁, hx₁, -, hfd₁⟩, hco₁, hess₁⟩ := curve_structure ℚbar (Gamma1 M) (T_mem_Gamma1 M)
  haveI := hfd₀
  haveI := hfd₁
  haveI := hco₀
  haveI := hco₁
  haveI := hess₀
  haveI := hess₁
  haveI : Module.Finite (FH Γ) (F1 M) := finite_incl hle j x₁ (hj.trans hx₁.symm) hfd₁
  haveI : Algebra.IsIntegral (FH Γ) (F1 M) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsAlgebraic (FH Γ) (F1 M) := Algebra.IsAlgebraic.of_finite _ _
  haveI : CharZero (FH Γ) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℚbar (FH Γ))
  haveI : CharZero (F1 M) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℚbar (F1 M))
  haveI : Algebra.IsSeparable (FH Γ) (F1 M) := inferInstance
  haveI hgen₀ : ∀ v : Place ℚbar (FH Γ), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI hgen₁ : ∀ w : Place ℚbar (F1 M), w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI : SMulCommClass ℚbar (FH Γ) (F1 M) :=
    ⟨fun r y z => by rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
      mul_left_comm]⟩
  set ω₀ : Ω[FH Γ⁄ℚbar] := x • D ℚbar (FH Γ) j with hω₀def

  have hmapreg : KaehlerDifferential.map ℚbar ℚbar (FH Γ) (F1 M) ω₀ ∈ Reg M := by
    have ha' : ∀ n : ℕ, qCoeff (⇑(restrictCusp (Subgroup.map_mono hΓ₁) f) : UpperHalfPlane → ℂ) n =
        (a n : ℂ) := ha
    obtain ⟨ω₁, hω₁, hq₁⟩ := exists_reg_F1 M (restrictCusp (Subgroup.map_mono hΓ₁) f) a ha'
    have hmap : KaehlerDifferential.map ℚbar ℚbar (FH Γ) (F1 M) ω₀ =
        algebraMap (FH Γ) (F1 M) x • D ℚbar (F1 M) (algebraMap (FH Γ) (F1 M) j) := by
      rw [hω₀def, LinearMap.map_smul, KaehlerDifferential.map_D, algebraMap_smul]
    have hq : qExpansionDiffAlong (IntermediateField.val (qExpFunctionFieldC ℚbar (Gamma1 M)))
        (KaehlerDifferential.map ℚbar ℚbar (FH Γ) (F1 M) ω₀) = red a := by
      rw [hmap, qE_smul_D, coe_algebraMap_incl, coe_algebraMap_incl, hj, hx]
      rfl
    rw [show KaehlerDifferential.map ℚbar ℚbar (FH Γ) (F1 M) ω₀ = ω₁ from
      qE1_injective M (hq.trans hq₁.symm)]
    exact hω₁

  intro v
  by_cases hω0 : ω₀ = 0
  · exact ⟨0, zero_mem _, by rw [hω0, zero_smul]⟩
  obtain ⟨w, hw⟩ := Place.exists_comap_eq_toValuationSubring (F' := F1 M) v
  have hwv : w.restrict (FH Γ) = v := Place.ext hw
  have hreg := localUnitDerivativeRegular_of_isCurveOver (K := ℚbar) (F' := F1 M)
  have htame : ∀ w' : Place ℚbar (F1 M), ((w'.ramificationIndex (FH Γ) : ℕ) : F1 M) ≠ 0 :=
    fun w' => Nat.cast_ne_zero.mpr (ne_of_gt (w'.ramificationIndex_pos (F := FH Γ)))
  have hformula := ordDifferential_map_eq (K := ℚbar) (F := FH Γ) (F' := F1 M) hreg htame hω0 w
  have hLHS : 0 ≤ w.ordDifferential (KaehlerDifferential.map ℚbar ℚbar (FH Γ) (F1 M) ω₀) :=
    ordDifferential_nonneg_of_mem w hmapreg
  rw [hformula, hwv] at hLHS
  have he : 1 ≤ (w.ramificationIndex (FH Γ) : ℤ) := by
    exact_mod_cast w.ramificationIndex_pos (F := FH Γ)
  have hv0 : 0 ≤ v.ordDifferential ω₀ := by
    by_contra hneg
    push Not at hneg
    have h1 : v.ordDifferential ω₀ ≤ -1 := by omega
    nlinarith
  exact ⟨v.differentialCoeff ω₀, mem_of_ord_nonneg v hv0, (v.differentialCoeff_smul_dCoord ω₀).symm⟩

end Descent

end ModularCurve.OmegaGammaHCharZeroProof
p2m_reactivate "P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.ModularCurve P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.ModularCurve.OmegaGammaHCharZeroProof"
p2m_reactivate "P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.ModularCurve"

p2m_open "ModularCurve~coeffEmb_injective~coeffMap_ofPowerSeries" in open _root_.P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.ModularCurve AlgebraicCurve in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : UpperHalfPlane → ℂ) n = (a n : ℂ))
    (x j : ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hj : (j : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) *
        ModularCurve.thetaL (AlgebraicClosure ℚ) (ModularCurve.jqModC (AlgebraicClosure ℚ)) =
      HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ)
        (PowerSeries.mk fun n => (a n : AlgebraicClosure ℚ))) :
    x • KaehlerDifferential.D (AlgebraicClosure ℚ)
        ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) j ∈
      AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
        ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) :=
  ModularCurve.OmegaGammaHCharZeroProof.main hΓ₁ f a ha x j hj hx

end
end S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
end P2MW
export P2MW.S_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq (solution)
