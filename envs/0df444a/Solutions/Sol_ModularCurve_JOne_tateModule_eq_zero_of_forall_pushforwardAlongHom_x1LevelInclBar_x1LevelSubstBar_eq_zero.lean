-- Prove2me | solution 1 for ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b392e245-af08-52ac-a712-069aa913a868

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHOperators

import Theorems.Thm_DualAssembly_injective_gram_of_forall_joint_eigenvector_mul
import Theorems.Thm_ModularCurve_sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia
import Theorems.Thm_ModularCurve_finrankAlong_x1LevelInclBar_eq_finrankAlong_x1LevelSubstBar
import Theorems.Thm_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
import Theorems.Thm_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul
import Theorems.Thm_ModularCurve_JOne_pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
import Theorems.Thm_ModularCurve_JOne_diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
import Theorems.Thm_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
import Theorems.Thm_ModularCurve_JH_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_and_pullbackAlongHom_diamondHBar_eq_diamondOneBar
import Theorems.Thm_ModularCurve_heckeDiamondCommuteBar
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
import Theorems.Thm_ModularCurve_finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_JOne_degeneracyPullbackInputs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply CuspForm.PeterssonCoset.mapGL_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.ShimuraCoveringData.mk.injEq ModularCurve.ShimuraCoveringData.mk.sizeOf_spec ModularCurve.ShimuraCoveringData.LiftData.mk.sizeOf_spec ModularCurve.ShimuraCoveringData.coe_coverHom ModularCurve.ShimuraCoveringData.LiftData.mk.injEq ModularCurve.coe_inclusionBar AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

open scoped TensorProduct

namespace GramE109

open TateModule

section Tmap

variable {p : ℕ} [Fact p.Prime]
variable {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable (p) in

noncomputable def tmap (f : A →+ B) : TateModule p A →ₗ[ℤ_[p]] TateModule p B where
  toFun x := ⟨fun n => f ((x : ℕ → A) n), fun n =>
    ⟨by
      show ((p ^ n : ℕ) : ℤ) • f ((x : ℕ → A) n) = 0
      rw [← map_zsmul, TateModule.torsion, map_zero],
     by
      show ((p : ℕ) : ℤ) • f ((x : ℕ → A) (n + 1)) = f ((x : ℕ → A) n)
      rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p A) : ℕ → A) n) = f ((x : ℕ → A) n) + f ((y : ℕ → A) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a.appr n : ℕ) : ℤ) • (x : ℕ → A) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → A) n)
    exact map_zsmul f _ _)

@[scoped simp] theorem tmap_apply (f : A →+ B) (x : TateModule p A) (n : ℕ) :
    ((tmap p f x : TateModule p B) : ℕ → B) n = f ((x : ℕ → A) n) := rfl

theorem tmap_comp (g : B →+ C) (f : A →+ B) : tmap p (g.comp f) = tmap p g ∘ₗ tmap p f :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem eq_zero_of_natCast_p_smul_eq_zero (x : TateModule p A) (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have hn := congrArg (fun y : TateModule p A => (y : ℕ → A) (n + 1)) h
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat] at hn
  rw [hn]
  rfl

theorem eq_zero_of_pow_p_smul_eq_zero (e : ℕ) (x : TateModule p A) (h : ((p : ℤ_[p]) ^ e) • x = 0) :
    x = 0 := by
  induction e generalizing x with
  | zero => rwa [pow_zero, one_smul] at h
  | succ e ih =>
    rw [pow_succ, mul_smul] at h
    exact eq_zero_of_natCast_p_smul_eq_zero x (ih _ h)

theorem isTorsionFree_tateModule : Module.IsTorsionFree ℤ_[p] (TateModule p A) := by
  refine ⟨fun r hr => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  intro x y hxy
  have h : r • (x - y) = 0 := by
    have := hxy
    simp only at this
    rw [smul_sub, this, sub_self]
  rw [← sub_eq_zero]
  rw [PadicInt.unitCoeff_spec hr0, mul_smul] at h
  have h' : ((p : ℤ_[p]) ^ r.valuation) • (x - y) = 0 :=
    ((PadicInt.unitCoeff hr0).isUnit.smul_eq_zero).mp h
  exact eq_zero_of_pow_p_smul_eq_zero _ _ h'

noncomputable def tmapEquiv (e : A ≃+ B) : TateModule p A ≃ₗ[ℤ_[p]] TateModule p B :=
  LinearEquiv.ofLinear (tmap p e.toAddMonoidHom) (tmap p e.symm.toAddMonoidHom)
    (LinearMap.ext fun x => Subtype.ext (funext fun n => by
      show e (e.symm ((x : ℕ → B) n)) = (x : ℕ → B) n
      exact e.apply_symm_apply _))
    (LinearMap.ext fun x => Subtype.ext (funext fun n => by
      show e.symm (e ((x : ℕ → A) n)) = (x : ℕ → A) n
      exact e.symm_apply_apply _))

theorem tmap_bijective_of_bijective (f : A →+ B) (hf : Function.Bijective f) :
    Function.Bijective (tmap p f) := by
  have h : tmap p f = (tmapEquiv (p := p) (AddEquiv.ofBijective f hf) : TateModule p A →ₗ[ℤ_[p]] TateModule p B) :=
    LinearMap.ext fun x => Subtype.ext (funext fun n => rfl)
  rw [h]
  exact (tmapEquiv (AddEquiv.ofBijective f hf)).bijective

theorem bijective_of_leftInverse_of_comp_bijective (f : A →+ B) (g : B →+ A) (u : B → B) (hu : Function.Bijective u)
    (hgf : ∀ a : A, g (f a) = a) (hfg : ∀ b : B, f (g b) = u b) : Function.Bijective f := by
  refine ⟨fun a a' h => by rw [← hgf a, ← hgf a', h], fun b => ?_⟩
  obtain ⟨b', hb'⟩ := hu.2 b
  exact ⟨g b', by rw [hfg, hb']⟩

end Tmap

section Frame

theorem xHFunctionFieldBar_bot (M : ℕ) :
    ModularCurve.xHFunctionFieldBar M ⊥ = ModularCurve.x1FunctionFieldBar M := by
  show ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldC ℚ M ⊥) =
    ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldC ℚ M)
  rw [ModularCurve.xHFunctionFieldC_bot]

theorem hasPrincipalDivisors_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  have h := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M ⊥
  rwa [xHFunctionFieldBar_bot] at h

theorem xHFunctionFieldBar_le_x1FunctionFieldBar (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.xHFunctionFieldBar M H ≤ ModularCurve.x1FunctionFieldBar M := by
  show IntermediateField.adjoin (AlgebraicClosure ℚ)
      (⇑(ModularCurve.coeffEmb (AlgebraicClosure ℚ)) '' (ModularCurve.xHFunctionFieldC ℚ M H : Set (LaurentSeries ℚ))) ≤
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      (⇑(ModularCurve.coeffEmb (AlgebraicClosure ℚ)) '' (ModularCurve.x1FunctionFieldC ℚ M : Set (LaurentSeries ℚ)))
  exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono (ModularCurve.xHFunctionFieldC_le_x1 ℚ M H))

theorem exists_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)] :
    ∃ (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
      (_ : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
        ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
          (x : LaurentSeries (AlgebraicClosure ℚ)))
      (hint : ι.toRingHom.IsIntegral),
      AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint := by
  have hle := xHFunctionFieldBar_le_x1FunctionFieldBar M H
  let ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M) :=
    IntermediateField.inclusion hle
  have hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι :=
    ModularCurve.finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar M H hle
  have hfin' : ι.toRingHom.Finite := hfin
  have hint : ι.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hfin'
  have hchar : CharZero ↥(ModularCurve.xHFunctionFieldBar M H) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)).injective
  have hsep : AlgebraicCurve.SeparableAlong (AlgebraicClosure ℚ) ι :=
    @Algebra.IsSeparable.of_integral ↥(ModularCurve.xHFunctionFieldBar M H) _ ↥(ModularCurve.x1FunctionFieldBar M) _
      (AlgebraicCurve.algebraAlong ι) _ (AlgebraicCurve.isIntegral_along ι hint) hchar
  exact ⟨ι, fun x => IntermediateField.coe_inclusion hle x, hint, AlgebraicCurve.fundamentalIdentityAlong ι hint hfin hsep⟩

theorem diamondOneBar_bijective (N d : ℕ) : Function.Bijective (ModularCurve.diamondOneBar N d) := by
  have h : (ModularCurve.diamondOneBar N d : ModularCurve.JOne N → ModularCurve.JOne N) =
      fun x => AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar N d) • x :=
    funext (ModularCurve.diamondOneBar_apply N d)
  rw [h]
  exact MulAction.bijective _

theorem exists_pull_bot (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N)] :
    ∃ pull : ModularCurve.JH N ⊥ →+ ModularCurve.JOne N,
      Function.Bijective (tmap p pull) ∧
      (∀ x : ModularCurve.JH N ⊥,
        pull (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) N ⊥ p x) =
          ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩ (pull x)) ∧
      (∀ x : ModularCurve.JH N ⊥,
        pull (ModularCurve.diamondHBar N ⊥ (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpN)) x) =
          ModularCurve.diamondOneBar N p (pull x)) := by
  obtain ⟨ι, hι, hιint, hιFI⟩ := exists_inclusion_xHFunctionFieldBar_x1FunctionFieldBar N ⊥
  have hin := ModularCurve.heckeDiamondInputsAll N
  have hinH := ModularCurve.heckeDiamondInputsHAll N ⊥
  have hS : ∀ d ∈ ({1} : Finset ℕ), Nat.Coprime d N := by
    intro d hd; rw [Finset.mem_singleton] at hd; subst hd; exact Nat.coprime_one_left N
  have hSH : ∀ (d : ℕ) (hd : d ∈ ({1} : Finset ℕ)), ZMod.unitOfCoprime d (hS d hd) ∈ (⊥ : Subgroup (ZMod N)ˣ) := by
    intro d hd
    have hd1 : d = 1 := Finset.mem_singleton.1 hd
    have : ZMod.unitOfCoprime d (hS d hd) = 1 := by
      ext; rw [ZMod.coe_unitOfCoprime, hd1, Nat.cast_one, Units.val_one]
    rw [this]; exact one_mem _
  have hHS : ∀ h ∈ (⊥ : Subgroup (ZMod N)ˣ), ∃! d : ℕ, d ∈ ({1} : Finset ℕ) ∧ (d : ZMod N) = ((h : (ZMod N)ˣ) : ZMod N) := by
    intro h hh
    have h1 : h = 1 := Subgroup.mem_bot.1 hh
    subst h1
    refine ⟨1, ⟨Finset.mem_singleton_self 1, by rw [Nat.cast_one, Units.val_one]⟩, ?_⟩
    rintro d ⟨hd, -⟩
    exact Finset.mem_singleton.1 hd
  obtain ⟨pull, push, c, m, hc, hm, hcm, hPinPull, -, -, -, hDeg, -, hNorm⟩ :=
    ModularCurve.JH.exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
      N ⊥ hin ι hι ({1} : Finset ℕ) hS hSH hHS
  have hpull_eq : ∀ x, pull x = AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI x := hPinPull hιint hιFI

  have hc1 : c = 1 ∧ m = 1 := by
    rw [Finset.card_singleton] at hcm
    exact ⟨Nat.eq_one_of_mul_eq_one_right hcm, Nat.eq_one_of_mul_eq_one_left hcm⟩
  obtain ⟨rfl, rfl⟩ := hc1
  have hgf : ∀ x, push (pull x) = x := fun x => by rw [hDeg, one_smul]
  have hfg : ∀ y, pull (push y) = ModularCurve.diamondOneBar N 1 y := fun y => by
    have h1 := hNorm y
    rw [Finset.sum_singleton, one_smul] at h1
    exact h1.symm
  have hbij : Function.Bijective (tmap p pull) :=
    tmap_bijective_of_bijective pull
      (bijective_of_leftInverse_of_comp_bijective pull push (ModularCurve.diamondOneBar N 1)
        (diamondOneBar_bijective N 1) hgf hfg)
  have hHC := ModularCurve.JH.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_and_pullbackAlongHom_diamondHBar_eq_diamondOneBar
    N ⊥ hin hinH ι hι hιint hιFI
  refine ⟨pull, hbij, fun x => ?_, fun x => ?_⟩
  · rw [hpull_eq, hpull_eq]; exact hHC.1 p Fact.out hpN x
  · rw [hpull_eq, hpull_eq]; exact hHC.2 p _ x

end Frame

section Eig

set_option maxHeartbeats 6400000 in

theorem eig_J1 (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (v : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N)) (a e : K) (hv : v ≠ 0)
    (hA : (tmap p (ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩).toAddMonoidHom).baseChange K v = a • v)
    (hD : (tmap p (ModularCurve.diamondOneBar N p).toAddMonoidHom).baseChange K v = e • v) :
    a ^ 2 ≠ (algebraMap ℤ_[p] K ((p + 1 : ℕ) : ℤ_[p])) ^ 2 * e := by
  classical
  haveI := hasPrincipalDivisors_x1FunctionFieldBar N
  obtain ⟨pull, hbij, hT, hDia⟩ := exists_pull_bot N p hpN
  have hpS : p ∉ (∅ : Set ℕ) := Set.notMem_empty p
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpN

  have hIT : (tmap p (ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩).toAddMonoidHom) ∘ₗ tmap p pull =
      tmap p pull ∘ₗ ModularCurve.tateGenOpH N ⊥ ∅ p (.T p Fact.out hpS hpN) := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩ (pull ((x : ℕ → ModularCurve.JH N ⊥) n)) =
      pull (ModularCurve.genOpH N ⊥ ∅ (.T p Fact.out hpS hpN) ((x : ℕ → ModularCurve.JH N ⊥) n))
    rw [ModularCurve.genOpH_T]
    exact (hT _).symm
  have hID : (tmap p (ModularCurve.diamondOneBar N p).toAddMonoidHom) ∘ₗ tmap p pull =
      tmap p pull ∘ₗ ModularCurve.tateGenOpH N ⊥ ∅ p (.dia (ZMod.unitOfCoprime p hcop)) := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show ModularCurve.diamondOneBar N p (pull ((x : ℕ → ModularCurve.JH N ⊥) n)) =
      pull (ModularCurve.genOpH N ⊥ ∅ (.dia (ZMod.unitOfCoprime p hcop)) ((x : ℕ → ModularCurve.JH N ⊥) n))
    rw [ModularCurve.genOpH_dia]
    exact (hDia _).symm

  let ΦE : TateModule p (ModularCurve.JH N ⊥) ≃ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne N) :=
    LinearEquiv.ofBijective (tmap p pull) hbij
  have hsymm_comp : ΦE.symm.toLinearMap ∘ₗ tmap p pull = LinearMap.id :=
    LinearMap.ext fun x => ΦE.symm_apply_apply x
  have hcomp_symm : tmap p pull ∘ₗ ΦE.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun y => ΦE.apply_symm_apply y
  have h1c : ΦE.symm.toLinearMap.baseChange K ∘ₗ (tmap p pull).baseChange K = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hsymm_comp, LinearMap.baseChange_id]
  have h2c : (tmap p pull).baseChange K ∘ₗ ΦE.symm.toLinearMap.baseChange K = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hcomp_symm, LinearMap.baseChange_id]
  have h1 : ∀ x : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JH N ⊥),
      ΦE.symm.toLinearMap.baseChange K ((tmap p pull).baseChange K x) = x := fun x => LinearMap.congr_fun h1c x
  have h2 : ∀ w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne N),
      (tmap p pull).baseChange K (ΦE.symm.toLinearMap.baseChange K w) = w := fun w => LinearMap.congr_fun h2c w
  have hinj : Function.Injective ((tmap p pull).baseChange K) := fun x y hxy => by
    rw [← h1 x, ← h1 y, hxy]

  have hcT := congrArg (LinearMap.baseChange K) hIT
  have hcD := congrArg (LinearMap.baseChange K) hID
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hcT hcD

  set u := ΦE.symm.toLinearMap.baseChange K v with hu
  have hΦu : (tmap p pull).baseChange K u = v := h2 v
  have hu0 : u ≠ 0 := fun h0 => hv (by rw [← hΦu, h0, map_zero])
  have hTu : (ModularCurve.tateGenOpH N ⊥ ∅ p (.T p Fact.out hpS hpN)).baseChange K u = a • u := by
    apply hinj
    rw [map_smul, hΦu, ← hA, ← hΦu]
    exact (LinearMap.congr_fun hcT u).symm
  have hDu : (ModularCurve.tateGenOpH N ⊥ ∅ p (.dia (ZMod.unitOfCoprime p hcop))).baseChange K u = e • u := by
    apply hinj
    rw [map_smul, hΦu, ← hD, ← hΦu]
    exact (LinearMap.congr_fun hcD u).symm
  exact ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia N p hpN ⊥ ∅ hpS
    (ModularCurve.heckeDiamondInputsHAll N ⊥) K hK u a e hu0 hTu (ZMod.unitOfCoprime p hcop) hDu

end Eig

end GramE109
p2m_reactivate "P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.GramE109"

namespace GramE109

section Deg

theorem finrankAlong_x1LevelInclBar_eq_mul (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) =
      (p + 1) * AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ)
        (ModularCurve.x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h0 := ModularCurve.finrankAlong_x1LevelInclBar_eq_finrankAlong_x1LevelSubstBar N p hpN
  rw [h0]
  obtain ⟨-, hβdef, -⟩ := ModularCurve.JOne.degeneracyPullbackInputs N p (N * p) (dvd_refl (N * p))
  show AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ)
      ((ModularCurve.x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).comp
        (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) N p)) = _
  rw [AlgebraicCurve.finrankAlong_comp, ModularCurve.finrankAlong_heckeBetaOneBar (AlgebraicClosure ℚ) N p hβdef, if_neg hpN]

end Deg
p2m_reactivate "P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.GramE109"

section Abstract

theorem commute_of_rel {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (A B Tt Dt : Module.End R V) (c : R) (hA : A = c • Tt) (hDB : Dt ∘ₗ B = A) (hTD : Tt ∘ₗ Dt = Dt ∘ₗ Tt)
    (hDinj : Function.Injective Dt) : Commute A B := by
  have hDA : Dt ∘ₗ A = A ∘ₗ Dt := by rw [hA, LinearMap.comp_smul, LinearMap.smul_comp, hTD]
  show A * B = B * A
  apply LinearMap.ext
  intro x
  apply hDinj
  have e1 : Dt ((A * B) x) = A (A x) := by
    rw [Module.End.mul_apply, ← LinearMap.comp_apply Dt A, hDA, LinearMap.comp_apply, ← LinearMap.comp_apply Dt B, hDB]
  have e2 : Dt ((B * A) x) = A (A x) := by
    rw [Module.End.mul_apply, ← LinearMap.comp_apply Dt B, hDB]
  rw [e1, e2]

theorem eigen_of_rel (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]
    (K : Type*) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (A B Tt Dt : Module.End ℤ_[p] V) (d c : ℕ) (hdeg : d = (p + 1) * c) (hd : 0 < d)
    (hA : A = ((c : ℕ) : ℤ_[p]) • Tt) (hDB : Dt ∘ₗ B = A)
    (heig : ∀ (v : K ⊗[ℤ_[p]] V) (a e : K), v ≠ 0 → Tt.baseChange K v = a • v → Dt.baseChange K v = e • v →
      a ^ 2 ≠ (algebraMap ℤ_[p] K ((p + 1 : ℕ) : ℤ_[p])) ^ 2 * e) :
    ∀ (v : K ⊗[ℤ_[p]] V) (a b : K), v ≠ 0 → A.baseChange K v = a • v → B.baseChange K v = b • v →
      a * b ≠ (algebraMap ℤ_[p] K ((d : ℕ) : ℤ_[p])) ^ 2 := by
  intro v a b hv hAv hBv heq
  rw [map_natCast] at heq
  have hcpos : 0 < c := by
    refine Nat.pos_of_ne_zero fun h => ?_
    have h' := hd
    rw [hdeg, h, mul_zero] at h'
    exact lt_irrefl 0 h'
  have hdK : ((d : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hcK : ((c : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hcpos.ne'
  have hdegK : ((d : ℕ) : K) = ((p + 1 : ℕ) : K) * ((c : ℕ) : K) := by rw [hdeg]; push_cast; ring
  by_cases ha : a = 0
  · apply hdK
    rw [ha, zero_mul] at heq
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).1 heq.symm
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, mul_zero] at heq
    exact hdK ((pow_eq_zero_iff (n := 2) (by norm_num)).1 heq.symm)

  have hAK : A.baseChange K = ((c : ℕ) : K) • Tt.baseChange K := by
    rw [hA, LinearMap.baseChange_smul, ← map_natCast (algebraMap ℤ_[p] K), algebraMap_smul]
  have hTv : Tt.baseChange K v = (a / ((c : ℕ) : K)) • v := by
    have h1 : ((c : ℕ) : K) • Tt.baseChange K v = a • v := by
      rw [← LinearMap.smul_apply, ← hAK]; exact hAv
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hcK, one_smul]

  have hDv : Dt.baseChange K v = (a / b) • v := by
    have h1 : Dt.baseChange K (B.baseChange K v) = A.baseChange K v := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hDB]
    rw [hBv, map_smul, hAv] at h1
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hne := heig v (a / ((c : ℕ) : K)) (a / b) hv hTv hDv
  apply hne
  rw [map_natCast]
  rw [hdegK] at heq
  field_simp
  linear_combination heq

end Abstract
p2m_reactivate "P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.GramE109"

section Gram

variable {p : ℕ} [Fact p.Prime]

theorem gram_abstract {J J' : Type} [AddCommGroup J] [AddCommGroup J']
    (pushα pushβ : J' →+ J) (pullα pullβ : J →+ J') (T δ : J →+ J) (d c : ℕ)
    (h11 : ∀ x : J, pushα (pullα x) = ((d : ℕ) : ℤ) • x) (h22 : ∀ x : J, pushβ (pullβ x) = ((d : ℕ) : ℤ) • x)
    (h33 : ∀ x : J, pushα (pullβ x) = ((c : ℕ) : ℤ) • T x) (h55 : ∀ x : J, δ (pushβ (pullα x)) = pushα (pullβ x))
    (hTδ : ∀ x : J, T (δ x) = δ (T x)) (hδ : Function.Bijective δ) (hdeg : d = (p + 1) * c) (hd : 0 < d)
    [Module.Finite ℤ_[p] (TateModule p J)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Algebra ℤ_[p] K] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (heig : ∀ (v : K ⊗[ℤ_[p]] TateModule p J) (a e : K), v ≠ 0 → (tmap p T).baseChange K v = a • v →
      (tmap p δ).baseChange K v = e • v → a ^ 2 ≠ (algebraMap ℤ_[p] K ((p + 1 : ℕ) : ℤ_[p])) ^ 2 * e)
    (w₀ w₁ : TateModule p J)
    (hGα : ∀ n : ℕ, pushα (pullα ((w₀ : ℕ → J) n) + pullβ ((w₁ : ℕ → J) n)) = 0)
    (hGβ : ∀ n : ℕ, pushβ (pullα ((w₀ : ℕ → J) n) + pullβ ((w₁ : ℕ → J) n)) = 0) :
    w₀ = 0 ∧ w₁ = 0 := by

  obtain ⟨A, hAdef⟩ : ∃ A : Module.End ℤ_[p] (TateModule p J), A = tmap p (pushα.comp pullβ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Module.End ℤ_[p] (TateModule p J), B = tmap p (pushβ.comp pullα) := ⟨_, rfl⟩
  obtain ⟨Tt, hTt⟩ : ∃ Tt : Module.End ℤ_[p] (TateModule p J), Tt = tmap p T := ⟨_, rfl⟩
  obtain ⟨Dt, hDt⟩ : ∃ Dt : Module.End ℤ_[p] (TateModule p J), Dt = tmap p δ := ⟨_, rfl⟩

  have hAw : ((d : ℕ) : ℤ_[p]) • w₀ + A w₁ = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    have h := hGα n
    rw [AddMonoidHom.map_add, h11] at h
    rw [TateModule.coe_add, Pi.add_apply, TateModule.natCast_padicInt_smul_apply, hAdef, tmap_apply,
      AddMonoidHom.comp_apply, TateModule.coe_zero, Pi.zero_apply]
    exact h
  have hBw : B w₀ + ((d : ℕ) : ℤ_[p]) • w₁ = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    have h := hGβ n
    rw [AddMonoidHom.map_add, h22] at h
    rw [TateModule.coe_add, Pi.add_apply, TateModule.natCast_padicInt_smul_apply, hBdef, tmap_apply,
      AddMonoidHom.comp_apply, TateModule.coe_zero, Pi.zero_apply]
    exact h

  have hA_T : A = ((c : ℕ) : ℤ_[p]) • Tt := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [hAdef, hTt, LinearMap.smul_apply, TateModule.natCast_padicInt_smul_apply, tmap_apply, tmap_apply,
      AddMonoidHom.comp_apply]
    exact h33 _
  have hDB : Dt ∘ₗ B = A := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [hDt, hBdef, hAdef, LinearMap.comp_apply, tmap_apply, tmap_apply, tmap_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.comp_apply]
    exact h55 _
  have hTD : Tt ∘ₗ Dt = Dt ∘ₗ Tt := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [hTt, hDt, LinearMap.comp_apply, LinearMap.comp_apply, tmap_apply, tmap_apply, tmap_apply, tmap_apply]
    exact hTδ _
  have hDinj : Function.Injective Dt := by
    rw [hDt]
    exact (tmap_bijective_of_bijective δ hδ).1
  have hAB : Commute A B := commute_of_rel A B Tt Dt _ hA_T hDB hTD hDinj

  haveI : Module.IsTorsionFree ℤ_[p] (TateModule p J) := isTorsionFree_tateModule
  have hd0 : ((d : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'

  have heig' : ∀ (v : K ⊗[ℤ_[p]] TateModule p J) (a e : K), v ≠ 0 → Tt.baseChange K v = a • v →
      Dt.baseChange K v = e • v → a ^ 2 ≠ (algebraMap ℤ_[p] K ((p + 1 : ℕ) : ℤ_[p])) ^ 2 * e := by
    rw [hTt, hDt]; exact heig
  have hEig := eigen_of_rel p K A B Tt Dt d c hdeg hd hA_T hDB heig'

  have hinj := DualAssembly.injective_gram_of_forall_joint_eigenvector_mul p K hK ((d : ℕ) : ℤ_[p]) hd0 A B hAB hEig
  have hz : (fun z : TateModule p J × TateModule p J => (((d : ℕ) : ℤ_[p]) • z.1 + A z.2, B z.1 + ((d : ℕ) : ℤ_[p]) • z.2)) (w₀, w₁) =
      (fun z : TateModule p J × TateModule p J => (((d : ℕ) : ℤ_[p]) • z.1 + A z.2, B z.1 + ((d : ℕ) : ℤ_[p]) • z.2)) (0, 0) := by
    show (((d : ℕ) : ℤ_[p]) • w₀ + A w₁, B w₀ + ((d : ℕ) : ℤ_[p]) • w₁) =
      (((d : ℕ) : ℤ_[p]) • (0 : TateModule p J) + A 0, B 0 + ((d : ℕ) : ℤ_[p]) • (0 : TateModule p J))
    rw [hAw, hBw, smul_zero, map_zero, map_zero, add_zero]
  have h := hinj hz
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Gram
p2m_reactivate "P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.GramE109"

section Main

theorem main (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (N * p))]
    (hαint : (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)).toRingHom.IsIntegral)
    (hβint : (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)))
    (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))))
    (hαN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαfin)
    (hβN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβfin)
    (w₀ w₁ : TateModule p (ModularCurve.JOne N))
    (hGα : ∀ n : ℕ,
        AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαfin hαN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαFI ((w₀ : ℕ → ModularCurve.JOne N) n) +
              AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI ((w₁ : ℕ → ModularCurve.JOne N) n)) = 0)
    (hGβ : ∀ n : ℕ,
        AlgebraicCurve.Pic0.pushforwardAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβfin hβN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαFI ((w₀ : ℕ → ModularCurve.JOne N) n) +
              AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI ((w₁ : ℕ → ModularCurve.JOne N) n)) = 0) :
    w₀ = 0 ∧ w₁ = 0 := by

  have hdeg := finrankAlong_x1LevelInclBar_eq_mul N p hpN
  have hdpos : 0 < AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ)
      (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) := by
    letI alg : Algebra ↥(ModularCurve.x1FunctionFieldBar N) ↥(ModularCurve.x1FunctionFieldBar (N * p)) :=
      AlgebraicCurve.algebraAlong (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p))
    letI mdl : Module ↥(ModularCurve.x1FunctionFieldBar N) ↥(ModularCurve.x1FunctionFieldBar (N * p)) := alg.toModule
    haveI : Module.Finite ↥(ModularCurve.x1FunctionFieldBar N) ↥(ModularCurve.x1FunctionFieldBar (N * p)) := hαfin
    exact Module.finrank_pos

  have h11 := ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul N p hpN
      hαint hβint hαFI hβFI hαfin hβfin hαN hβN
  have h22 := ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul N p hpN
      hαint hβint hαFI hβFI hαfin hβfin hαN hβN
  have h33 := ModularCurve.JOne.pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
      N p hpN hαint hβint hαFI hβFI hαfin hβfin hαN hβN
  have h55 := ModularCurve.JOne.diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
      N p hpN hαint hβint hαFI hβFI hαfin hβfin hαN hβN
  rw [← ModularCurve.finrankAlong_x1LevelInclBar_eq_finrankAlong_x1LevelSubstBar N p hpN] at h22

  have hcomm := ModularCurve.heckeDiamondCommuteBar N (Sum.inl ⟨p, Fact.out⟩) (Sum.inr p)
  have hTδ : ∀ x : ModularCurve.JOne N,
      ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩ (ModularCurve.diamondOneBar N p x) =
        ModularCurve.diamondOneBar N p (ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩ x) := by
    intro x
    have h := LinearMap.congr_fun hcomm x
    rw [Module.End.mul_apply, Module.End.mul_apply, ModularCurve.heckeDiamondGenBar_inl,
      ModularCurve.heckeDiamondGenBar_inr] at h
    exact h

  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne N)) := ModularCurve.moduleFinite_padicInt_tateModule_jOne N p
  haveI : CharZero (AlgebraicClosure ℚ_[p]) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
  have hK : Function.Injective (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])]
    exact (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  exact gram_abstract _ _ _ _ (ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩).toAddMonoidHom
    (ModularCurve.diamondOneBar N p).toAddMonoidHom _ _ h11 h22 h33 h55 hTδ (diamondOneBar_bijective N p) hdeg hdpos
    (AlgebraicClosure ℚ_[p]) hK (fun v a e hv hA hD => eig_J1 N p hpN (AlgebraicClosure ℚ_[p]) hK v a e hv hA hD)
    w₀ w₁ hGα hGβ

end Main
p2m_reactivate "P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.GramE109"

end GramE109
p2m_reactivate "P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.GramE109"

theorem solution
    (N M p : ℕ) [NeZero N] [NeZero M] [Fact p.Prime] (hpN : ¬ p ∣ N) (hNM : N ∣ M) (hNpM : N * p ∣ M) (hM : M = N * p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    (hαint : (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM).toRingHom.IsIntegral)
    (hβint : (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM).toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM))
    (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM))
    (hαN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαfin)
    (hβN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβfin) :
    ∀ w₀ w₁ : TateModule p (ModularCurve.JOne N),
      (∀ n : ℕ,
        AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint hαfin hαN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint hαFI ((w₀ : ℕ → ModularCurve.JOne N) n) +
              AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint hβFI ((w₁ : ℕ → ModularCurve.JOne N) n)) = 0) →
      (∀ n : ℕ,
        AlgebraicCurve.Pic0.pushforwardAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint hβfin hβN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint hαFI ((w₀ : ℕ → ModularCurve.JOne N) n) +
              AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint hβFI ((w₁ : ℕ → ModularCurve.JOne N) n)) = 0) →
      w₀ = 0 ∧ w₁ = 0 := by
  subst hM
  intro w₀ w₁ hGα hGβ
  exact GramE109.main N p hpN hαint hβint hαFI hβFI hαfin hβfin hαN hβN w₀ w₁ hGα hGβ

end S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero
end P2MW
export P2MW.S_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero (solution)
