-- Prove2me | solution 1 for ModularCurve.exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d3149cc2-20c6-58a3-a55a-71739688f803

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke
import Theorems.Thm_FinFlatHopf_dualPoints_equiv_monoidHom
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
import Theorems.Thm_ModularCurve_finiteFlatModel_comul_comp_heckeEndo
import Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
import Theorems.Thm_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_JZero_cardinalityAJ_genusFF
import Theorems.Thm_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois TateModule.instModule TateModule.instSMul ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateMap_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve
open scoped TensorProduct

namespace L3Nat

theorem dualPoints_equiv_comp_map
    (B : Type) [CommRing B] (H : Type) [CommRing H] [HopfAlgebra B H]
    [Coalgebra.IsCocomm B H] [Module.Finite B H] [Module.Free B H]
    (Ω : Type) [Field Ω] [Algebra B Ω]
    (eD : WithConv (CartierDual B H →ₐ[B] Ω) ≃* (WithConv (H →ₐ[B] Ω) →* Ωˣ))
    (heD : ∀ (g : WithConv (CartierDual B H →ₐ[B] Ω)) (f : WithConv (H →ₐ[B] Ω)),
        ((eD g f : Ωˣ) : Ω) =
          Algebra.TensorProduct.productMap (WithConv.ofConv g) (AlgHom.id B Ω)
            ((TensorProduct.congr (CartierDual.ofDual B H) (LinearEquiv.refl B Ω))
              ((dualTensorHomEquiv B H Ω).symm (WithConv.ofConv f).toLinearMap)))
    (q : H →ₐc[B] H) (g : WithConv (CartierDual B H →ₐ[B] Ω)) (f : WithConv (H →ₐ[B] Ω)) :
    ((eD (WithConv.toConv ((WithConv.ofConv g).comp
        (CartierDual.map q : CartierDual B H →ₐ[B] CartierDual B H))) f : Ωˣ) : Ω) =
      ((eD g (WithConv.toConv ((WithConv.ofConv f).comp (q : H →ₐ[B] H))) : Ωˣ) : Ω) := by
  rw [heD, heD]

  set mq : CartierDual B H →ₐ[B] CartierDual B H := (CartierDual.map q : CartierDual B H →ₐ[B] CartierDual B H)
    with hmq
  set e := TensorProduct.congr (CartierDual.ofDual B H) (LinearEquiv.refl B Ω) with he

  have hA : (Algebra.TensorProduct.map mq (AlgHom.id B Ω)).toLinearMap ∘ₗ e.toLinearMap =
      e.toLinearMap ∘ₗ TensorProduct.map (q : H →ₗ[B] H).dualMap LinearMap.id :=
    TensorProduct.ext' fun δ ω => by
      show mq (CartierDual.ofDual B H δ) ⊗ₜ[B] ω = CartierDual.ofDual B H ((q : H →ₗ[B] H).dualMap δ) ⊗ₜ[B] ω
      congr 1

  have hB : dualTensorHom B H Ω ∘ₗ TensorProduct.map (q : H →ₗ[B] H).dualMap LinearMap.id =
      LinearMap.lcomp B Ω (q : H →ₗ[B] H) ∘ₗ dualTensorHom B H Ω :=
    TensorProduct.ext' fun δ ω => by
      apply LinearMap.ext
      intro h
      show dualTensorHom B H Ω (((q : H →ₗ[B] H).dualMap δ) ⊗ₜ[B] ω) h =
        dualTensorHom B H Ω (δ ⊗ₜ[B] ω) (q h)
      rw [dualTensorHom_apply, dualTensorHom_apply]
      rfl
  have hdTH : ∀ w : Module.Dual B H ⊗[B] Ω, dualTensorHomEquiv B H Ω w = dualTensorHom B H Ω w :=
    fun w => rfl
  set F : H →ₗ[B] Ω := (WithConv.ofConv f).toLinearMap with hF
  have hBw : ∀ w : Module.Dual B H ⊗[B] Ω,
      dualTensorHom B H Ω (TensorProduct.map (q : H →ₗ[B] H).dualMap LinearMap.id w) =
        (dualTensorHom B H Ω w) ∘ₗ (q : H →ₗ[B] H) := fun w => LinearMap.congr_fun hB w
  have hB' : TensorProduct.map (q : H →ₗ[B] H).dualMap LinearMap.id ((dualTensorHomEquiv B H Ω).symm F) =
      (dualTensorHomEquiv B H Ω).symm (F ∘ₗ (q : H →ₗ[B] H)) := by
    apply (dualTensorHomEquiv B H Ω).injective
    rw [hdTH, hBw, ← hdTH, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hcomp : ((WithConv.ofConv f).comp (q : H →ₐ[B] H)).toLinearMap = F ∘ₗ (q : H →ₗ[B] H) := rfl
  have hofConv : WithConv.ofConv (WithConv.toConv ((WithConv.ofConv f).comp (q : H →ₐ[B] H))) =
      (WithConv.ofConv f).comp (q : H →ₐ[B] H) := rfl
  have hofConv' : WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g).comp mq)) =
      (WithConv.ofConv g).comp mq := rfl
  rw [hofConv, hofConv', hcomp, ← hB']
  have hAw : ∀ w : Module.Dual B H ⊗[B] Ω,
      Algebra.TensorProduct.map mq (AlgHom.id B Ω) (e w) =
        e (TensorProduct.map (q : H →ₗ[B] H).dualMap LinearMap.id w) := fun w => LinearMap.congr_fun hA w
  rw [← hAw]

  have hC : (Algebra.TensorProduct.productMap ((WithConv.ofConv g).comp mq) (AlgHom.id B Ω)).toLinearMap =
      (Algebra.TensorProduct.productMap (WithConv.ofConv g) (AlgHom.id B Ω)).toLinearMap ∘ₗ
        (Algebra.TensorProduct.map mq (AlgHom.id B Ω)).toLinearMap :=
    TensorProduct.ext' fun φ ω => rfl
  exact LinearMap.congr_fun hC _

theorem baseChangeEquiv_map_tensorMap
    (R : Type) (S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    (ε : CartierDual S (S ⊗[R] A) ≃ₐc[S] S ⊗[R] CartierDual R A)
    (hε : ∀ (s t : S) (φ : CartierDual R A) (a : A),
        CartierDual.pairing S (S ⊗[R] A) (ε.symm (s ⊗ₜ[R] φ)) (t ⊗ₜ[R] a) =
          s * t * algebraMap R S (CartierDual.pairing R A φ a))
    (q : A →ₐc[R] A) (x : CartierDual S (S ⊗[R] A)) :
    ε (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id S S) q) x) =
      Algebra.TensorProduct.map (AlgHom.id S S) (CartierDual.map q : CartierDual R A →ₐ[R] CartierDual R A) (ε x) := by
  set ψ := Bialgebra.TensorProduct.map (BialgHom.id S S) q with hψ

  have key : ∀ (s : S) (φ : CartierDual R A),
      ε (CartierDual.map ψ (ε.symm (s ⊗ₜ[R] φ))) = s ⊗ₜ[R] CartierDual.map q φ := by
    intro s φ
    suffices hsuff : CartierDual.map ψ (ε.symm (s ⊗ₜ[R] φ)) = ε.symm (s ⊗ₜ[R] CartierDual.map q φ) by
      rw [hsuff, BialgEquiv.apply_symm_apply]

    apply (CartierDual.toDual S (S ⊗[R] A)).injective
    refine TensorProduct.AlgebraTensorModule.ext fun t a => ?_
    show (CartierDual.map ψ (ε.symm (s ⊗ₜ[R] φ))) (t ⊗ₜ[R] a) = (ε.symm (s ⊗ₜ[R] CartierDual.map q φ)) (t ⊗ₜ[R] a)
    have h1 := hε s t φ (q a)
    have h2 := hε s t (CartierDual.map q φ) a
    simp only [CartierDual.pairing_apply, CartierDual.map_apply] at h1 h2
    rw [h2]
    exact h1

  let L₁ : S ⊗[R] CartierDual R A →+ S ⊗[R] CartierDual R A :=
    ε.toCoalgEquiv.toLinearEquiv.toLinearMap.toAddMonoidHom.comp
      ((CartierDual.map ψ).toCoalgHom.toLinearMap.toAddMonoidHom.comp
        ε.symm.toCoalgEquiv.toLinearEquiv.toLinearMap.toAddMonoidHom)
  let L₂ : S ⊗[R] CartierDual R A →+ S ⊗[R] CartierDual R A :=
    (Algebra.TensorProduct.map (AlgHom.id S S)
      (CartierDual.map q : CartierDual R A →ₐ[R] CartierDual R A)).toRingHom.toAddMonoidHom
  have hL₁ : ∀ y, L₁ y = ε (CartierDual.map ψ (ε.symm y)) := fun _ => rfl
  have hL₂ : ∀ y, L₂ y = Algebra.TensorProduct.map (AlgHom.id S S)
      (CartierDual.map q : CartierDual R A →ₐ[R] CartierDual R A) y := fun _ => rfl
  have hL : ∀ y, L₁ y = L₂ y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | tmul s φ =>
      rw [hL₁, hL₂, key]
      rfl
  have hx := hL (ε x)
  rw [hL₁, hL₂, BialgEquiv.symm_apply_apply] at hx
  exact hx

end L3Nat

namespace L3Body

@[reducible] def galAction {G : Type*} [Group G] {J : Type*} [AddCommGroup J] [DistribMulAction G J]
    {S : Type*} [Ring S] [Module S J] (W : Submodule S J)
    (hW : ∀ (g : G) {x : J}, x ∈ W → g • x ∈ W) : DistribMulAction G ↥W where
  smul g x := ⟨g • (x : J), hW g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : J))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : J))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : J) (y : J))

section CharAction

variable (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]

noncomputable def ptsAct (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) where
  toFun f := WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars (GaloisRep.ratLocalizedAt p)).comp
    (WithConv.ofConv f))
  map_one' := by
    apply congrArg WithConv.toConv
    apply AlgHom.ext
    intro a
    show σ ((1 : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) a) = (1 : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) a
    simp only [AlgHom.convOne_apply]
    exact ((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars (GaloisRep.ratLocalizedAt p)).commutes _
  map_mul' f g := by
    apply congrArg WithConv.toConv
    rw [AlgHom.comp_convMul_distrib]
    rfl

theorem ptsAct_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (a : A) :
    ptsAct p A σ f a = σ (f a) := rfl

theorem ptsAct_mul (σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : ptsAct p A (σ * τ) = (ptsAct p A σ).comp (ptsAct p A τ) := by
  apply MonoidHom.ext; intro f; apply congrArg WithConv.toConv; apply AlgHom.ext; intro a; rfl

theorem ptsAct_one : ptsAct p A 1 = MonoidHom.id _ := by
  apply MonoidHom.ext; intro f; apply congrArg WithConv.toConv; apply AlgHom.ext; intro a; rfl

noncomputable def charSMul (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) :
    WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ :=
  (Units.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toMonoidHom).comp (χ.comp (ptsAct p A σ⁻¹))

theorem charSMul_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    ((charSMul p A σ χ f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = σ ((χ (ptsAct p A σ⁻¹ f) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) :=
  rfl

noncomputable scoped instance charAction :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ)) where
  smul σ χ := Additive.ofMul (charSMul p A σ (Additive.toMul χ))
  one_smul χ := by
    apply congrArg Additive.ofMul
    apply MonoidHom.ext; intro f; apply Units.ext
    rw [charSMul_apply, inv_one, ptsAct_one]
    rfl
  mul_smul σ τ χ := by
    apply congrArg Additive.ofMul
    apply MonoidHom.ext; intro f; apply Units.ext
    show ((charSMul p A (σ * τ) (Additive.toMul χ) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((charSMul p A σ (charSMul p A τ (Additive.toMul χ)) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [charSMul_apply, charSMul_apply, charSMul_apply, mul_inv_rev, ptsAct_mul]
    rfl
  smul_zero σ := by
    apply congrArg Additive.ofMul
    apply MonoidHom.ext; intro f; apply Units.ext
    show ((charSMul p A σ 1 f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((1 : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [charSMul_apply, MonoidHom.one_apply, Units.val_one, map_one]
  smul_add σ χ χ' := by
    apply congrArg Additive.ofMul
    apply MonoidHom.ext; intro f; apply Units.ext
    show ((charSMul p A σ (Additive.toMul χ * Additive.toMul χ') f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((charSMul p A σ (Additive.toMul χ) f * charSMul p A σ (Additive.toMul χ') f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [charSMul_apply, MonoidHom.mul_apply, Units.val_mul, map_mul, Units.val_mul, charSMul_apply, charSMul_apply]

theorem toMul_smul_apply (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ)) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    ((Additive.toMul (σ • χ) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      σ ((Additive.toMul χ (ptsAct p A σ⁻¹ f) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) :=
  rfl

end CharAction

end L3Body
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq.L3Body"

open L3Body in
set_option maxHeartbeats 16000000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]
    [Module.Finite (GaloisRep.ratLocalizedAt p) A] [Module.Flat (GaloisRep.ratLocalizedAt p) A]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) A] :
    letI := heckeModuleBar N
    ∀ e : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
        ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)),
      (∀ f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : A, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) →
      ∀ φ : HeckeAlg → (A →ₐ[GaloisRep.ratLocalizedAt p] A),
        (∀ (t : HeckeAlg) (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : A, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N)) →
      ∀ ψ : HeckeAlg →
          ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A),
        (∀ t : HeckeAlg,
            (ψ t : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p]
                (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) =
              Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ t)) →
      ∃ θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) ≃ₐc[ZMod p]
          (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A,
        ∀ t : HeckeAlg,
          (θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p]
              (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A).comp (CartierDual.map (ψ t)) =
            (ψ t).comp (θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p]
              (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) := by
  letI := heckeModuleBar N
  intro e he_add he_gal φ hφ ψ hψ
  classical

  haveI hDVR : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI hfreeA : Module.Free (GaloisRep.ratLocalizedAt p) A := Module.free_of_flat_of_isLocalRing
  have hcomm : HeckeOperatorsCommuteBar N := ModularCurve.heckeOperatorsCommuteBar N
  haveI hsmc := ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar N hcomm

  obtain ⟨B, hBpow, hBl, hBr, hBnd, hBgal, hBhecke⟩ :=
    ModularCurve.exists_pairing_nsmul_eq_zero_galois_hecke N p (Fact.out : p.Prime).ne_zero

  have hcomul : ∀ t : HeckeAlg,
      Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := A) ∘ₗ (φ t).toLinearMap =
          TensorProduct.map (φ t).toLinearMap (φ t).toLinearMap ∘ₗ
            Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := A) ∧
        Coalgebra.counit (R := GaloisRep.ratLocalizedAt p) (A := A) ∘ₗ (φ t).toLinearMap =
          Coalgebra.counit (R := GaloisRep.ratLocalizedAt p) (A := A) := by
    intro t
    have hiff : ∀ x : JZero N,
        x ∈ Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1) ↔ x ∈ heckeTorsion (JZero N) (Ideal.span {((p : ℕ) : HeckeAlg)}) := by
      intro x
      rw [Submodule.mem_torsionBy_iff, mem_heckeTorsion_iff, pow_one, ← Int.cast_smul_eq_zsmul HeckeAlg,
        Int.cast_natCast]
      constructor
      · intro hx t ht
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ht
        rw [mul_smul, hx, smul_zero]
      · intro hx
        exact hx _ (Ideal.mem_span_singleton_self _)
    let eP : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) (Ideal.span {((p : ℕ) : HeckeAlg)})) :=
      e.trans (Equiv.subtypeEquivRight hiff)
    exact ModularCurve.finiteFlatModel_comul_comp_heckeEndo N p _ A eP
      (fun f g => Subtype.ext (by
        show ((e (f * g) : JZero N)) = (e f : JZero N) + (e g : JZero N)
        rw [he_add]; rfl))
      φ (fun t f g hfg => hφ t f g hfg) t
  let φB : HeckeAlg → (A →ₐc[GaloisRep.ratLocalizedAt p] A) := fun t =>
    BialgHom.ofAlgHom (φ t)
      (AlgHom.ext fun a => LinearMap.congr_fun (hcomul t).2 a)
      (AlgHom.ext fun a => (LinearMap.congr_fun (hcomul t).1 a).symm)
  have hφB : ∀ t, (φB t : A →ₐ[GaloisRep.ratLocalizedAt p] A) = φ t := fun t => rfl

  have hcardA : Nat.card (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) = Module.finrank (GaloisRep.ratLocalizedAt p) A :=
    GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf p A
  obtain ⟨eD, heD, heDgal⟩ := FinFlatHopf.dualPoints_equiv_monoidHom (GaloisRep.ratLocalizedAt p) A (AlgebraicClosure ℚ) hcardA

  letI galM₁ : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) :=
    galAction _ (fun σ x hx => by
      rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← smul_comm σ, hx, smul_zero])

  have hgalM₂ : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) (f f' : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), (∀ x, f' x = σ (f x)) →
      ((Additive.toMul (σ • Additive.ofMul χ) f' : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        σ ((χ f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
    intro σ χ f f' hff'
    rw [toMul_smul_apply]
    have hf : ptsAct p A σ⁻¹ f' = f := by
      show WithConv.toConv _ = f
      rw [← WithConv.toConv_ofConv f]
      apply congrArg WithConv.toConv
      apply AlgHom.ext
      intro a
      show σ⁻¹ (f' a) = f a
      rw [hff' a, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [hf]
    rfl

  have hpZ : ∀ x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)), (p : ℤ) • (x : JZero N) = 0 := by
    intro x
    have hx := x.2
    rw [Submodule.mem_torsionBy_iff] at hx
    have h1 : ((p : ℤ) ^ 1) • (x : JZero N) = (p : ℤ) • (x : JZero N) :=
      congrArg (fun c : ℤ => c • (x : JZero N)) (pow_one (p : ℤ))
    calc (p : ℤ) • (x : JZero N) = ((p : ℤ) ^ 1) • (x : JZero N) := h1.symm
      _ = 0 := hx
  have hpT : ∀ x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)), p • x = 0 := by
    intro x
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero, ← natCast_zsmul]
    exact hpZ x
  letI modT : Module (ZMod p) ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) := AddCommGroup.zmodModule hpT
  haveI hfinT : Finite ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) := by
    have hfin := JZero.finite_torsion_pow_of_cardinalityAJ N p (JZero.cardinalityAJ_genusFF N p) 1
    let ι : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ 1)) :=
      fun x => ⟨(x : JZero N), by
        rw [AlgebraicCurve.Pic0.mem_torsion]
        have h2 : (((p ^ 1 : ℕ) : ℤ)) • (x : JZero N) = (p : ℤ) • (x : JZero N) :=
          congrArg (fun c : ℤ => c • (x : JZero N)) (by norm_num)
        exact h2.trans (hpZ x)⟩
    exact Finite.of_injective ι (fun x y h => Subtype.ext (congrArg Subtype.val h :))
  haveI hmf : Module.Finite (ZMod p) ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) := Module.Finite.of_finite
  have hcardT : Nat.card ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) = p ^ Module.finrank (ZMod p) ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) := by
    have hc := @Module.natCard_eq_pow_finrank (ZMod p) ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) _ _ modT hmf
    rwa [Nat.card_zmod] at hc
  have hrankA : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) A = p ^ a :=
    ⟨_, by rw [← hcardA, Nat.card_congr e, hcardT]⟩
  have hrankD : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) (CartierDual (GaloisRep.ratLocalizedAt p) A) = p ^ a := by
    obtain ⟨a, ha⟩ := hrankA
    refine ⟨a, ?_⟩
    rw [← ha]
    exact (CartierDual.toDual (GaloisRep.ratLocalizedAt p) A).finrank_eq.trans (Module.finrank_linearMap_self (GaloisRep.ratLocalizedAt p) (GaloisRep.ratLocalizedAt p) A)

  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpN : ∀ x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)), p • (x : JZero N) = 0 := fun x => by rw [← natCast_zsmul]; exact hpZ x
  have hmemT : ∀ y : JZero N, p • y = 0 → y ∈ Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1) := by
    intro y hy
    rw [Submodule.mem_torsionBy_iff]
    have h1 : ((p : ℤ) ^ 1) • y = (p : ℤ) • y := congrArg (fun c : ℤ => c • y) (pow_one (p : ℤ))
    rw [h1, natCast_zsmul]
    exact hy
  have hB0r : ∀ x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)), B (x : JZero N) 0 = 1 := by
    intro x
    have h := hBr (x : JZero N) 0 0 (hpN x) (smul_zero _) (smul_zero _)
    rw [add_zero] at h
    have hne : B (x : JZero N) 0 ≠ 0 := fun h0 => by
      have := hBpow (x : JZero N) 0 (hpN x) (smul_zero _); rw [h0, zero_pow hp0] at this; exact zero_ne_one this
    exact (mul_eq_left₀ hne).mp h.symm
  have hB0l : ∀ y : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)), B 0 (y : JZero N) = 1 := by
    intro y
    have h := hBl 0 0 (y : JZero N) (smul_zero _) (smul_zero _) (hpN y)
    rw [add_zero] at h
    have hne : B 0 (y : JZero N) ≠ 0 := fun h0 => by
      have := hBpow 0 (y : JZero N) (smul_zero _) (hpN y); rw [h0, zero_pow hp0] at this; exact zero_ne_one this
    exact (mul_eq_left₀ hne).mp h.symm
  have he_one : e 1 = 0 := by
    have h := he_add 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hBne : ∀ (x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), B (x : JZero N) ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) ≠ 0 := by
    intro x f h0
    have := hBpow (x : JZero N) ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) (hpN x) (hpN _)
    rw [h0, zero_pow hp0] at this
    exact zero_ne_one this
  let χ : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) → (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) := fun x =>
    { toFun := fun f => Units.mk0 _ (hBne x f)
      map_one' := Units.ext (by
        show B (x : JZero N) ((e 1 : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) = 1
        rw [he_one, ZeroMemClass.coe_zero, hB0r])
      map_mul' := fun f g => Units.ext (by
        show B (x : JZero N) ((e (f * g) : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) =
          B (x : JZero N) ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) * B (x : JZero N) ((e g : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N)
        rw [he_add, Submodule.coe_add, hBr _ _ _ (hpN x) (hpN _) (hpN _)]) }
  have hχ : ∀ (x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), ((χ x f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      B (x : JZero N) ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) := fun _ _ => rfl
  let Φ₀ : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) →+ Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) :=
    { toFun := fun x => Additive.ofMul (χ x)
      map_zero' := by
        apply congrArg Additive.ofMul
        apply MonoidHom.ext; intro f; apply Units.ext
        rw [hχ, ZeroMemClass.coe_zero, hB0l, MonoidHom.one_apply, Units.val_one]
      map_add' := fun x x' => by
        apply congrArg Additive.ofMul
        apply MonoidHom.ext; intro f; apply Units.ext
        show ((χ (x + x') f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((χ x f * χ x' f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        rw [Units.val_mul, hχ, hχ, hχ, Submodule.coe_add, hBl _ _ _ (hpN x) (hpN x') (hpN _)] }
  have hΦ₀ : ∀ (x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), ((Additive.toMul (Φ₀ x) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      B (x : JZero N) ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) := fun _ _ => rfl

  have hΦ₀inj : Function.Injective Φ₀ := by
    refine (injective_iff_map_eq_zero Φ₀).mpr (fun z h => ?_)
    apply Subtype.ext
    refine hBnd (z : JZero N) (hpN z) (fun y hy => ?_)
    have hy' := hmemT y hy
    obtain ⟨f, hf⟩ := e.surjective ⟨y, hy'⟩
    have h1 := congrArg (fun c : Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) => ((Additive.toMul c f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h
    simp only [hΦ₀, hf] at h1
    rw [h1]
    rfl

  have hcardD : Nat.card (WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) = Module.finrank (GaloisRep.ratLocalizedAt p) (CartierDual (GaloisRep.ratLocalizedAt p) A) :=
    GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf p (CartierDual (GaloisRep.ratLocalizedAt p) A)
  have hfinrkD : Module.finrank (GaloisRep.ratLocalizedAt p) (CartierDual (GaloisRep.ratLocalizedAt p) A) = Module.finrank (GaloisRep.ratLocalizedAt p) A :=
    (CartierDual.toDual (GaloisRep.ratLocalizedAt p) A).finrank_eq.trans (Module.finrank_linearMap_self (GaloisRep.ratLocalizedAt p) (GaloisRep.ratLocalizedAt p) A)
  have hcard_eq : Nat.card (Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ)) = Nat.card ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) := by
    rw [Nat.card_congr (Additive.ofMul (α := WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ)).symm,
      ← Nat.card_congr eD.toEquiv, hcardD, hfinrkD, ← hcardA, Nat.card_congr e]
  have hΦ₀bij : Function.Bijective Φ₀ := by
    haveI : Finite (Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard_eq]; exact Nat.card_pos.ne')
    exact hΦ₀inj.bijective_of_nat_card_le hcard_eq.le
  let Φ : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) ≃+ Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) := AddEquiv.ofBijective Φ₀ hΦ₀bij
  have hΦB : ∀ (x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) (f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), ((Additive.toMul (Φ x) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      B (x : JZero N) ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) := fun _ _ => rfl

  have hΦgal : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))), Φ (σ • x) = σ • Φ x := by
    intro σ x
    show Additive.ofMul (χ (σ • x)) = σ • Additive.ofMul (χ x)
    apply congrArg Additive.ofMul
    apply MonoidHom.ext; intro f; apply Units.ext
    show ((χ (σ • x) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((charSMul p A σ (χ x) f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [charSMul_apply, hχ, hχ]
    have hef : ((e f : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) = σ • ((e (ptsAct p A σ⁻¹ f) : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) :=
      he_gal σ (ptsAct p A σ⁻¹ f) f (fun h => by
        show f h = σ (σ⁻¹ (f h))
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
    rw [hef]
    exact (hBgal σ (x : JZero N) _ (hpN x) (hpN _)).trans rfl

  have he_gal' : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), (∀ x : A, g x = σ (f x)) → e g = σ • e f :=
    fun σ f g h => Subtype.ext (he_gal σ f g h)
  let e₂ : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ Additive (WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ) :=
    eD.toEquiv.trans Additive.ofMul
  have he₂_add : ∀ f g : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e₂ (f * g) = e₂ f + e₂ g := by
    intro f g; show Additive.ofMul (eD (f * g)) = Additive.ofMul (eD f) + Additive.ofMul (eD g)
    rw [map_mul]; rfl
  have he₂_gal : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), (∀ x : CartierDual (GaloisRep.ratLocalizedAt p) A, g x = σ (f x)) → e₂ g = σ • e₂ f := by
    intro σ f g hfg
    let τ : AlgebraicClosure ℚ ≃ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ :=
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars (GaloisRep.ratLocalizedAt p)
    have hg : g = WithConv.toConv (τ.toAlgHom.comp (WithConv.ofConv f)) := by
      rw [← WithConv.toConv_ofConv g]
      apply congrArg WithConv.toConv
      apply AlgHom.ext
      intro x
      exact hfg x
    have hh : ∀ h : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        WithConv.toConv (τ.symm.toAlgHom.comp (WithConv.ofConv h)) = ptsAct p A σ⁻¹ h := by
      intro h
      apply congrArg WithConv.toConv
      apply AlgHom.ext
      intro x
      rfl
    show Additive.ofMul (eD g) = σ • Additive.ofMul (eD f)
    apply congrArg Additive.ofMul
    apply MonoidHom.ext
    intro h
    apply Units.ext
    show ((eD g h : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((charSMul p A σ (eD f) h : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [charSMul_apply, hg, heDgal τ f h, hh h]
    rfl
  obtain ⟨⟨g, hg, -⟩, hbij⟩ :=
    HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two p hp2
      A hrankA e he_add he_gal' (CartierDual (GaloisRep.ratLocalizedAt p) A) hrankD e₂ he₂_add he₂_gal Φ hΦgal
  have hgb : Function.Bijective g := hbij g hg

  have S_HECKE : ∀ t : HeckeAlg,
      (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A).comp (CartierDual.map (φB t) : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] CartierDual (GaloisRep.ratLocalizedAt p) A) =
        (φ t).comp (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A) := by
    intro t
    apply AlgHom.ext
    intro x

    apply HopfAlgebra.eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt p A
    intro F

    let F' : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv F
    let G : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv ((WithConv.ofConv F').comp (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A))
    let F'' : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv (F.comp (φ t))
    let P₁ : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv ((WithConv.ofConv G).comp
      (CartierDual.map (φB t) : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] CartierDual (GaloisRep.ratLocalizedAt p) A))
    let P₂ : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv ((WithConv.ofConv F'').comp (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A))
    have hP : P₁ = P₂ := by
      apply eD.injective
      apply MonoidHom.ext
      intro h
      apply Units.ext

      have hL := L3Nat.dualPoints_equiv_comp_map (GaloisRep.ratLocalizedAt p) A (AlgebraicClosure ℚ) eD heD (φB t) G h
      have hG : eD G = Additive.toMul (Φ (e F')) := by
        have := hg F'
        exact Additive.ofMul.injective (by (first | exact this | simpa using this | (have h__ := this; simp at h__; exact h__)))
      have hG'' : eD P₂ = Additive.toMul (Φ (e F'')) := by
        have := hg F''
        exact Additive.ofMul.injective (by (first | exact this | simpa using this | (have h__ := this; simp at h__; exact h__)))
      let h' : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv ((WithConv.ofConv h).comp (φB t : A →ₐ[GaloisRep.ratLocalizedAt p] A))
      have heh' : ((e h' : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) = t • ((e h : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) := hφ t h h' (fun a => rfl)
      have heF'' : ((e F'' : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) = t • ((e F' : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) := hφ t F' F'' (fun a => rfl)
      rw [hL, hG, hG'', hΦB, hΦB]
      show B ((e F' : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) ((e h' : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) = B ((e F'' : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N) ((e h : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1))) : JZero N)
      rw [heh', heF'', hBhecke t _ _ (hpN _) (hpN _)]
    exact congrArg (fun P : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) => (WithConv.ofConv P) x) hP

  obtain ⟨ε, hε⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul (GaloisRep.ratLocalizedAt p) (ZMod p) A
  have S_BC : ∃ θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) ≃ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A,
      ∀ t : HeckeAlg,
        (θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A).comp
            (CartierDual.map (ψ t)) =
          (ψ t).comp (θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) := by

    let bcg : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] CartierDual (GaloisRep.ratLocalizedAt p) A →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A :=
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g
    have hbcg_fun : ∀ y, bcg y = Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A) y := by
      intro y
      exact AlgHom.congr_fun (Bialgebra.TensorProduct.map_toAlgHom (BialgHom.id (ZMod p) (ZMod p)) g) y
    have hbcg_bij : Function.Bijective bcg := by
      have hb := (Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod p ≃ₐ[ZMod p] ZMod p)
        (AlgEquiv.ofBijective (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A) hgb)).bijective
      have hfun : ⇑(Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod p ≃ₐ[ZMod p] ZMod p)
          (AlgEquiv.ofBijective (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A) hgb)) = ⇑bcg := by
        funext y
        rw [Algebra.TensorProduct.congr_apply, hbcg_fun]
        rfl
      rwa [hfun] at hb
    let θ₀ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A := bcg.comp (ε : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] CartierDual (GaloisRep.ratLocalizedAt p) A)
    have hθ₀_bij : Function.Bijective θ₀ := hbcg_bij.comp ε.toEquiv.bijective
    refine ⟨BialgEquiv.ofBijective θ₀ hθ₀_bij, fun t => ?_⟩
    apply BialgHom.ext
    intro x
    show θ₀ (CartierDual.map (ψ t) x) = ψ t (θ₀ x)

    have hψfun : ∀ y : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A, ψ t y = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φB t) y := by
      intro y
      have h1 := AlgHom.congr_fun (hψ t) y
      have h2 : ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φB t) : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) y) =
          Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ t) y := by
        rw [Bialgebra.TensorProduct.map_toAlgHom]; rfl
      exact h1.trans h2.symm
    have hmapψ : CartierDual.map (ψ t) x =
        CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φB t)) x :=
      CartierDual.ext (fun a => by rw [CartierDual.map_apply, CartierDual.map_apply, hψfun])
    show bcg (ε (CartierDual.map (ψ t) x)) = ψ t (bcg (ε x))
    rw [hmapψ, L3Nat.baseChangeEquiv_map_tensorMap (GaloisRep.ratLocalizedAt p) (ZMod p) A ε hε (φB t) x, hbcg_fun, hbcg_fun, hψfun,
      ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, S_HECKE t]
    show _ = ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φB t) : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)
      (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (g : CartierDual (GaloisRep.ratLocalizedAt p) A →ₐ[GaloisRep.ratLocalizedAt p] A) (ε x)))
    rw [Bialgebra.TensorProduct.map_toAlgHom, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  exact S_BC

end S_ModularCurve_exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq
end P2MW
export P2MW.S_ModularCurve_exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq (solution)
