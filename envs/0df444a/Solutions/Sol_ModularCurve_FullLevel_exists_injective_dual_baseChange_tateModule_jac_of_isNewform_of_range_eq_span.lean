-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/90e36b2b-0740-517a-8884-5bfcddf08fb2

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import Theorems.Thm_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
import Theorems.Thm_CuspForm_IsAdelicLiftOf_eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam HeckeIntegralSeam.finite_padicInt_quotient_span_p AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply AutomorphicForm.mem_borelSubgroup_iff"
p2m_attr_erase "simp" "AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped TensorProduct MatrixGroups ModularForm

noncomputable section

namespace Ws41
namespace E4

section Functorial

variable {p : ℕ} [Fact p.Prime] {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']

def tateMap (p : ℕ) [Fact p.Prime] (f : M →+ M') : TateModule p M →ₗ[ℤ_[p]] TateModule p M' where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p M) : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a • x : TateModule p M) : ℕ → M) n) =
      (((a • (⟨fun n => f ((x : ℕ → M) n), _⟩ : TateModule p M')) : TateModule p M') : ℕ → M') n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem coe_tateMap_apply (f : M →+ M') (x : TateModule p M) (n : ℕ) :
    ((tateMap p f x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n) := rfl

theorem tateMap_comp_apply (f : M →+ M') (g : M' →+ M'') (x : TateModule p M) :
    tateMap p (g.comp f) x = tateMap p g (tateMap p f x) :=
  Subtype.ext (funext fun _ => rfl)

theorem tateMap_injective (f : M →+ M') (hf : Function.Injective f) :
    Function.Injective (tateMap p f) := by
  intro x y h
  refine Subtype.ext (funext fun n => hf ?_)
  exact congrArg (fun z : TateModule p M' => (z : ℕ → M') n) h

theorem tateMap_naturality (u : M →+ M') (S : M →+ M) (T : M' →+ M')
    (h : ∀ m, u (S m) = T (u m)) (x : TateModule p M) :
    tateMap p u (tateMap p S x) = tateMap p T (tateMap p u x) :=
  Subtype.ext (funext fun n => h _)

theorem tateMap_eq_rep (S : AddMonoid.End M) :
    tateMap p (S : M →+ M) = TateModule.rep p M (AddMonoid.End M) S :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

end Functorial

section Components

open ModularCurve.FullLevel

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]

def evalHom (ζ : Idx q) : Jac q M' →+ jacComp q M' where
  toFun x := x.eval ζ
  map_zero' := Jac.eval_zero ζ
  map_add' x y := Jac.eval_add x y ζ

@[scoped simp] theorem evalHom_apply (ζ : Idx q) (x : Jac q M') : evalHom q M' ζ x = x.eval ζ := rfl

def tateJacEquiv : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')) where
  toFun x ζ := tateMap lam (evalHom q M' ζ) x
  map_add' x y := funext fun ζ => map_add _ x y
  map_smul' a x := funext fun ζ => LinearMap.map_smul _ a x
  invFun y := ⟨fun n => Jac.mk fun ζ => ((y ζ : TateModule lam (jacComp q M')) : ℕ → jacComp q M') n, fun n =>
    ⟨Jac.ext fun ζ => by
        rw [Jac.eval_zsmul, Jac.eval_mk, Jac.eval_zero]
        exact TateModule.torsion (y ζ) n,
     Jac.ext fun ζ => by
        rw [Jac.eval_zsmul, Jac.eval_mk, Jac.eval_mk]
        exact TateModule.compat (y ζ) n⟩⟩
  left_inv x := Subtype.ext (funext fun n => Jac.ext fun ζ => by rw [Jac.eval_mk]; rfl)
  right_inv y := funext fun ζ => Subtype.ext (funext fun n => by
    show (Jac.mk fun ζ' => ((y ζ' : TateModule lam (jacComp q M')) : ℕ → jacComp q M') n).eval ζ = _
    rw [Jac.eval_mk])

@[scoped simp] theorem coe_tateJacEquiv_apply (x : TateModule lam (Jac q M')) (ζ : Idx q) (n : ℕ) :
    ((tateJacEquiv q M' lam x ζ : TateModule lam (jacComp q M')) : ℕ → jacComp q M') n =
      ((x : ℕ → Jac q M') n).eval ζ := rfl

theorem tateJacEquiv_apply (x : TateModule lam (Jac q M')) (ζ : Idx q) :
    tateJacEquiv q M' lam x ζ = tateMap lam (evalHom q M' ζ) x := rfl

theorem tateJacEquiv_tateEnd_mapIdx (T : Idx q → (jacComp q M' →+ jacComp q M')) (s : Idx q → Idx q)
    (x : TateModule lam (Jac q M')) (ζ : Idx q) :
    tateJacEquiv q M' lam (tateEnd q M' lam (Jac.mapIdx T s) x) ζ = tateMap lam (T ζ) (tateJacEquiv q M' lam x (s ζ)) :=
  Subtype.ext (funext fun n => Jac.mapIdx_eval T s _ ζ)

theorem tateJacEquiv_tateGL2_redQ (hGL : GL2Laws q M') (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (x : TateModule lam (Jac q M')) (ζ : Idx q) :
    tateJacEquiv q M' lam (tateGL2 q M' lam (redQ q γ) x) ζ = tateMap lam (levelOp q M' ζ γ⁻¹) (tateJacEquiv q M' lam x ζ) := by
  rw [tateGL2, MonoidHom.comp_apply, gl2Jac_redQ hGL γ hγ]
  exact Subtype.ext (funext fun n => rfl)

theorem tateJacEquiv_tateGL2_diagOneElem (hGL : GL2Laws q M') (d : (ZMod q)ˣ)
    (x : TateModule lam (Jac q M')) (ζ : Idx q) :
    tateJacEquiv q M' lam (tateGL2 q M' lam (diagOneElem q d) x) ζ = tateJacEquiv q M' lam x (ζ.pow d⁻¹) := by
  rw [tateGL2, MonoidHom.comp_apply, gl2Jac_diagOneElem hGL d]
  exact Subtype.ext (funext fun n => rfl)

theorem tateJacEquiv_tateHecke_heckeGen (hHC : HeckeGenCommute q M') (ℓ : Nat.Primes) (hℓqM : ¬ (ℓ : ℕ) ∣ q * M')
    (hq : (ℓ : ℕ).Coprime q) (hqM : (ℓ : ℕ).Coprime (q ^ 2 * M'))
    (x : TateModule lam (Jac q M')) (ζ : Idx q) :
    tateJacEquiv q M' lam (tateHecke q M' lam (ModularCurve.heckeGen ℓ) x) ζ =
      tateMap lam ((ModularCurve.diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹).comp
        (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
          ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ))
        (tateJacEquiv q M' lam x (ζ.pow (ZMod.unitOfCoprime ℓ hq)⁻¹)) := by
  rw [tateHecke, RingHom.comp_apply, heckeJac_heckeGen hHC ℓ]
  exact Subtype.ext (funext fun n => heckeGenJac_eval ℓ.2 hℓqM hq hqM _ ζ)

end Components

namespace Arch

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.AdelicLevel AdelicDock

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) : AdeleRing R K)

theorem mapMatrix_arch_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (adeleArch R K).mapMatrix (archMat R K g) = g := by
  ext i j; simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]

theorem mapMatrix_fin_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (adeleFin R K).mapMatrix (archMat R K g) = 1 := by
  ext i j; simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply]

theorem archMat_one : archMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_archMat, map_one]) (by rw [mapMatrix_fin_archMat, map_one])

theorem archMat_mul (g h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    archMat R K (g * h) = archMat R K g * archMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_archMat, mapMatrix_arch_archMat, mapMatrix_arch_archMat])
    (by rw [map_mul, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mul_one])

def archEmbed : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := archMat R K g
      inv := archMat R K ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix _ _ _)
      val_inv := by rw [← archMat_mul, Units.mul_inv, archMat_one]
      inv_val := by rw [← archMat_mul, Units.inv_mul, archMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat_mul R K _ _)

@[scoped simp] theorem coe_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ((archEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = archMat R K g := rfl

theorem glArch_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) : glArch R K (archEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, coe_archEmbed]; rfl

theorem glFin_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) : glFin R K (archEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, coe_archEmbed, Units.val_one]; rfl

end Generic

section Rat

local notation "𝔸GL" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

def realEquiv (w : InfinitePlace ℚ) : w.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)

def realToInfAdele : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun w => (realEquiv w).symm.toRingHom

theorem realToInfAdele_apply (x : ℝ) (w : InfinitePlace ℚ) : realToInfAdele x w = (realEquiv w).symm x := rfl

def realToArch : GL (Fin 2) ℝ →* 𝔸GL :=
  (archEmbed (𝓞 ℚ) ℚ).comp (Matrix.GeneralLinearGroup.map realToInfAdele)

theorem glFin_realToArch (A : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (realToArch A) = 1 := by
  rw [realToArch, MonoidHom.comp_apply, glFin_archEmbed]

theorem glArch_realToArch (A : GL (Fin 2) ℝ) :
    glArch (𝓞 ℚ) ℚ (realToArch A) = Matrix.GeneralLinearGroup.map realToInfAdele A := by
  rw [realToArch, MonoidHom.comp_apply, glArch_archEmbed]

theorem ratArchGL2_def (g : 𝔸GL) : LanglandsTunnell.ratArchGL2 g =
    Matrix.GeneralLinearGroup.map (realEquiv default).toRingHom (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) := rfl

theorem ratArchGL2_realToArch (A : GL (Fin 2) ℝ) : LanglandsTunnell.ratArchGL2 (realToArch A) = A := by
  rw [ratArchGL2_def, glArch_realToArch]
  ext i j
  simp [archComponent_apply, Matrix.GeneralLinearGroup.map_apply, realToInfAdele_apply]

end Rat

end Arch
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch"

section Determination
open UpperHalfPlane

private def _root_.Ws41.E4.toGL (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![y, x; 0, 1] (by simp [Matrix.det_fin_two]; exact hy.ne')

p2m_export "Ws41.E4" "toGL"
@[scoped simp] theorem toGL_coe (x y : ℝ) (hy : 0 < y) :
    ((toGL x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![y, x; 0, 1] := rfl

@[scoped simp] theorem toGL_apply (x y : ℝ) (hy : 0 < y) (i j : Fin 2) :
    (toGL x y hy : GL (Fin 2) ℝ) i j = !![y, x; 0, 1] i j := rfl

theorem toGL_det (x y : ℝ) (hy : 0 < y) : (toGL x y hy).det.val = y := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem toGL_mem_glpos (x y : ℝ) (hy : 0 < y) : toGL x y hy ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos, toGL_det]; exact hy

theorem toGL_smul_I (τ : ℍ) : toGL τ.re τ.im τ.im_pos • UpperHalfPlane.I = τ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [toGL_det]; exact τ.im_pos)]
  simp only [num, denom, toGL_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', UpperHalfPlane.coe_I,
    Complex.ofReal_zero, zero_mul, Complex.ofReal_one, zero_add, div_one]
  apply Complex.ext <;> simp

theorem slash_toGL_apply_I {k : ℤ} (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] toGL τ.re τ.im τ.im_pos) UpperHalfPlane.I = F τ * (τ.im : ℂ) ^ (k - 1) := by
  have hσ : σ (toGL τ.re τ.im τ.im_pos) = .refl ℝ ℂ := if_pos (by rw [toGL_det]; exact τ.im_pos)
  rw [ModularForm.slash_apply, toGL_smul_I, toGL_det, hσ, ContinuousAlgEquiv.refl_apply, abs_of_pos τ.im_pos]
  simp [denom]

theorem eq_of_forall_slash_apply_I {k : ℤ} {F₁ F₂ : ℍ → ℂ}
    (h : ∀ M : GL (Fin 2) ℝ, M ∈ Matrix.GLPos (Fin 2) ℝ →
      (F₁ ∣[k] M) UpperHalfPlane.I = (F₂ ∣[k] M) UpperHalfPlane.I) : F₁ = F₂ := by
  funext τ
  have := h _ (toGL_mem_glpos τ.re τ.im τ.im_pos)
  rw [slash_toGL_apply_I, slash_toGL_apply_I] at this
  exact mul_right_cancel₀ (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr τ.im_pos.ne')) this

end Determination
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch"

section ComponentMap

open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

abbrev Γfull : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M'

abbrev dQ (u : ℤ_[q]ˣ) : GL (Fin 2) ℚ_[q] := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u)

variable {q M'} {Φ : 𝔸GL → ℂ}

def IsComponentFn (y : AdelicSpan Φ) (u : ℤ_[q]ˣ) (G : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : 𝔸GL, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
    (AdelicSpan.toFn Φ y).toFn (h * padicToAdelic q (dQ q u)) = (G ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

theorem IsComponentFn.unique {y : AdelicSpan Φ} {u : ℤ_[q]ˣ} {G₁ G₂ : UpperHalfPlane → ℂ}
    (h₁ : IsComponentFn y u G₁) (h₂ : IsComponentFn y u G₂) : G₁ = G₂ := by
  refine eq_of_forall_slash_apply_I (k := 2) fun A hA => ?_
  have hfin := Arch.glFin_realToArch A
  have hrat := Arch.ratArchGL2_realToArch A
  have hpos : LanglandsTunnell.ratArchGL2 (Arch.realToArch A) ∈ Matrix.GLPos (Fin 2) ℝ := by rw [hrat]; exact hA
  rw [← hrat, ← h₁ _ hfin hpos, ← h₂ _ hfin hpos]

def IsComponent (y : AdelicSpan Φ) (u : ℤ_[q]ˣ) (F : CuspForm (Γfull q M') 2) : Prop :=
  IsComponentFn (q := q) y u ⇑F

namespace IsComponent

variable {y y₁ y₂ : AdelicSpan Φ} {u : ℤ_[q]ˣ} {F F₁ F₂ : CuspForm (Γfull q M') 2}

theorem isComponentFn (h : IsComponent y u F) : IsComponentFn (q := q) y u ⇑F := h

theorem unique (h₁ : IsComponent y u F₁) (h₂ : IsComponent y u F₂) : F₁ = F₂ :=
  DFunLike.coe_injective (IsComponentFn.unique h₁ h₂)

theorem coe_eq {G : UpperHalfPlane → ℂ} (h₁ : IsComponent y u F) (h₂ : IsComponentFn (q := q) y u G) : ⇑F = G :=
  IsComponentFn.unique h₁ h₂

theorem zero : IsComponent (0 : AdelicSpan Φ) u (0 : CuspForm (Γfull q M') 2) := fun h _ _ => by
  rw [CuspForm.coe_zero, SlashAction.zero_slash]; rfl

theorem add (h₁ : IsComponent y₁ u F₁) (h₂ : IsComponent y₂ u F₂) : IsComponent (y₁ + y₂) u (F₁ + F₂) :=
  fun h hh hp => by
    rw [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply, ← h₁ h hh hp, ← h₂ h hh hp]; rfl

theorem smul (c : ℂ) (h₁ : IsComponent y u F) : IsComponent (c • y) u (c • F) := fun h hh hp => by
  rw [CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash, UpperHalfPlane.σ, if_pos (Matrix.mem_glpos _ |>.mp hp),
    ContinuousAlgEquiv.refl_apply, Pi.smul_apply, smul_eq_mul, ← h₁ h hh hp]; rfl

end IsComponent
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch"

end ComponentMap
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch"

end Ws41.E4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped TensorProduct MatrixGroups ModularForm

noncomputable section

namespace Ws41
namespace E4

open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

section LocalKit

variable (q : ℕ) [Fact q.Prime]

abbrev diagZ (u : ℤ_[q]ˣ) : GL (Fin 2) ℤ_[q] := NumberField.AdelicLevel.diagOne u

theorem map_diagZ (u : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) (diagZ q u) = dQ q u := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, NumberField.AdelicLevel.diagOne_coe_apply, diagZ, dQ]
  fin_cases i <;> fin_cases j <;> simp

theorem map_toZMod_diagZ (u : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := q)) (diagZ q u) =
      CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, NumberField.AdelicLevel.diagOne_coe_apply, diagZ,
    CuspidalType.diagElem]
  fin_cases i <;> fin_cases j <;> simp

theorem map_mem_gl2CongruenceSubgroup_one_of_map_toZMod_eq_one {m : GL (Fin 2) ℤ_[q]}
    (hm : Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := q)) m = 1) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) m ∈
      FLT.SmoothVectors.gl2CongruenceSubgroup q 1 := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q le_rfl]
  intro i j
  have hij : PadicInt.toZMod ((m : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j) = 0 := by
    have e := congrArg (fun g : GL (Fin 2) (ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) i j) hm
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at e
    rw [map_sub, e]
    fin_cases i <;> fin_cases j <;> simp
  have hmem : (m : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j ∈
      Ideal.span {(q : ℤ_[q]) ^ 1} := by
    rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hij
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr hmem
  have hcoe : ((Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) m : GL (Fin 2) ℚ_[q]) :
      Matrix (Fin 2) (Fin 2) ℚ_[q]) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j =
      (((m : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j : ℤ_[q]) : ℚ_[q]) := by
    rw [Matrix.GeneralLinearGroup.map_apply, PadicInt.coe_sub]
    congr 1
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.sub_apply, hcoe, PadicInt.padic_norm_e_of_padicInt]
  exact_mod_cast hnorm

theorem dQ_mem_gl2CongruenceSubgroup_one {w : ℤ_[q]ˣ} (hw : PadicInt.toZMod (w : ℤ_[q]) = 1) :
    dQ q w ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 := by
  rw [← map_diagZ]
  apply map_mem_gl2CongruenceSubgroup_one_of_map_toZMod_eq_one
  rw [map_toZMod_diagZ]
  have h1 : Units.map PadicInt.toZMod.toMonoidHom w = 1 := Units.ext (by simpa using hw)
  rw [h1]
  ext i j
  simp only [CuspidalType.diagElem, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

theorem dQ_mem_gl2CongruenceSubgroup_zero (u : ℤ_[q]ˣ) : dQ q u ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
  rw [LocalNewvector.mem_gl2CongruenceSubgroup_zero_iff]
  constructor
  · intro i j
    rw [← map_diagZ, Matrix.GeneralLinearGroup.map_apply]
    exact PadicInt.norm_le_one _
  · intro i j
    rw [← map_diagZ, ← map_inv, Matrix.GeneralLinearGroup.map_apply]
    exact PadicInt.norm_le_one _

theorem exists_unit_toZMod_eq (a : (ZMod q)ˣ) : ∃ u : ℤ_[q]ˣ, PadicInt.toZMod (u : ℤ_[q]) = a := by
  obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := q)) (a : ZMod q)
  have hu : IsUnit x := by
    by_contra hna
    have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[q] :=
      (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 hna)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx] at hmem
    exact a.ne_zero hmem
  exact ⟨hu.unit, by rw [IsUnit.unit_spec, hx]⟩

def unitLift (a : (ZMod q)ˣ) : ℤ_[q]ˣ := (exists_unit_toZMod_eq q a).choose

theorem toZMod_unitLift (a : (ZMod q)ˣ) : PadicInt.toZMod (unitLift q a : ℤ_[q]) = a :=
  (exists_unit_toZMod_eq q a).choose_spec

theorem map_toZMod_unitLift (a : (ZMod q)ˣ) : Units.map PadicInt.toZMod.toMonoidHom (unitLift q a) = a :=
  Units.ext (by simpa using toZMod_unitLift q a)

end LocalKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Torsor

open ModularCurve.FullLevel

variable {q : ℕ} [Fact q.Prime]

theorem Idx.pow_pow (ζ : Idx q) (a b : (ZMod q)ˣ) : (ζ.pow a).pow b = ζ.pow (a * b) := by
  apply Idx.ext
  simp only [Idx.val_pow, Units.val_mul, ZMod.val_mul, ← pow_mul]
  have := pow_mod_orderOf ζ.val (((a : ZMod q)).val * ((b : ZMod q)).val)
  rw [← ζ.isPrimitiveRoot.eq_orderOf] at this
  exact this.symm

theorem Idx.pow_one' (ζ : Idx q) : ζ.pow 1 = ζ := by
  apply Idx.ext
  haveI : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩
  rw [Idx.val_pow, Units.val_one, ZMod.val_one, pow_one]

theorem Idx.pow_pow_inv (ζ : Idx q) (a : (ZMod q)ˣ) : (ζ.pow a).pow a⁻¹ = ζ := by
  rw [Idx.pow_pow, mul_inv_cancel, Idx.pow_one']

theorem Idx.pow_inv_pow (ζ : Idx q) (a : (ZMod q)ˣ) : (ζ.pow a⁻¹).pow a = ζ := by
  rw [Idx.pow_pow, inv_mul_cancel, Idx.pow_one']

theorem Idx.pow_left_injective (ζ : Idx q) : Function.Injective fun e : (ZMod q)ˣ => ζ.pow e := by
  intro a b h
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h' := congrArg Idx.val h
  simp only [Idx.val_pow] at h'
  have := ζ.isPrimitiveRoot.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'
  exact Units.ext (ZMod.val_injective q this)

theorem Idx.exists_pow_eq (ζ₀ ζ : Idx q) : ∃ e : (ZMod q)ˣ, ζ₀.pow e = ζ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : 0 < q := (Fact.out : q.Prime).pos
  obtain ⟨i, hi, h⟩ := ζ₀.isPrimitiveRoot.eq_pow_of_pow_eq_one ζ.isPrimitiveRoot.pow_eq_one
  have hcop : i.Coprime q := (ζ₀.isPrimitiveRoot.pow_iff_coprime hq i).1 (h ▸ ζ.isPrimitiveRoot)
  refine ⟨ZMod.unitOfCoprime i hcop, Idx.ext ?_⟩
  rw [Idx.val_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, h]

def idxEquiv (ζ₀ : Idx q) : (ZMod q)ˣ ≃ Idx q :=
  Equiv.ofBijective (fun e => ζ₀.pow e) ⟨Idx.pow_left_injective ζ₀, fun ζ => Idx.exists_pow_eq ζ₀ ζ⟩

@[scoped simp] theorem idxEquiv_apply (ζ₀ : Idx q) (e : (ZMod q)ˣ) : idxEquiv ζ₀ e = ζ₀.pow e := rfl

theorem pow_idxEquiv_symm (ζ₀ ζ : Idx q) : ζ₀.pow ((idxEquiv ζ₀).symm ζ) = ζ :=
  (idxEquiv ζ₀).apply_symm_apply ζ

theorem idxEquiv_symm_pow (ζ₀ ζ : Idx q) (d : (ZMod q)ˣ) :
    (idxEquiv ζ₀).symm (ζ.pow d) = (idxEquiv ζ₀).symm ζ * d := by
  apply (idxEquiv ζ₀).injective
  rw [Equiv.apply_symm_apply, idxEquiv_apply, ← Idx.pow_pow, pow_idxEquiv_symm]

end Torsor
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Comp

variable {q : ℕ} [Fact q.Prime] {Φ : 𝔸GL → ℂ}

theorem toFn_mul_padicToAdelic_of_mem_fixed (y : AdelicSpan Φ) {U : Subgroup (GL (Fin 2) ℚ_[q])}
    (hfix : y ∈ fixedSubmodule U (AdelicSpan Φ)) {m : GL (Fin 2) ℚ_[q]} (hm : m ∈ U) (z : 𝔸GL) :
    (AdelicSpan.toFn Φ y).toFn (z * padicToAdelic q m) = (AdelicSpan.toFn Φ y).toFn z := by
  have h := hfix m hm
  have := congrArg (fun w => (AdelicSpan.toFn Φ w).toFn z) h
  simpa [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul] using this

theorem toFn_padic_smul_apply (m : GL (Fin 2) ℚ_[q]) (y : AdelicSpan Φ) (z : 𝔸GL) :
    (AdelicSpan.toFn Φ (m • y)).toFn z = (AdelicSpan.toFn Φ y).toFn (z * padicToAdelic q m) := by
  simp [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

theorem IsComponentFn.of_toZMod_eq {y : AdelicSpan Φ}
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (AdelicSpan Φ))
    {u u' : ℤ_[q]ˣ} (huu' : PadicInt.toZMod (u : ℤ_[q]) = PadicInt.toZMod (u' : ℤ_[q]))
    {G : UpperHalfPlane → ℂ} (h : IsComponentFn (q := q) y u G) : IsComponentFn (q := q) y u' G := by
  intro hh hfin hpos
  have hw : PadicInt.toZMod ((u⁻¹ * u' : ℤ_[q]ˣ) : ℤ_[q]) = 1 := by
    have hu : PadicInt.toZMod ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) * PadicInt.toZMod (u : ℤ_[q]) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, ← huu', hu]
  have hk := dQ_mem_gl2CongruenceSubgroup_one q hw
  have e : dQ q u' = dQ q u * dQ q (u⁻¹ * u') := by
    rw [← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [e, map_mul, ← mul_assoc, toFn_mul_padicToAdelic_of_mem_fixed y hfix hk]
  exact h hh hfin hpos

variable (q)
variable {M' : ℕ} [NeZero M']
  {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hΦg : g.IsAdelicLiftOf Φ)
  {V : Type} [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
  (f : V →ₗ[ℂ] AdelicSpan Φ)
  (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
  (hfrange : LinearMap.range f =
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))

abbrev VK (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V] : Type :=
  ↥(fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)

include hΦg hf hfrange

theorem mem_span_apply (v : V) :
    f v ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ) := by
  rw [← hfrange]; exact LinearMap.mem_range_self f v

theorem mem_fixed_apply (v : VK q V) :
    f (v : V) ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (AdelicSpan Φ) := by
  rw [mem_fixedSubmodule_iff]
  intro m hm
  rw [← hf, (mem_fixedSubmodule_iff.1 v.2) m hm]

theorem exists_isComponent (v : VK q V) (u : ℤ_[q]ˣ) :
    ∃ F : CuspForm (Γfull q M') 2, IsComponent (f (v : V)) u F :=
  CuspForm.IsAdelicLiftOf.exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule
    q hΦg (f (v : V)) (mem_span_apply q hΦg f hf hfrange v) (mem_fixed_apply q hΦg f hf hfrange v) u

def compF (u : ℤ_[q]ˣ) : VK q V →ₗ[ℂ] CuspForm (Γfull q M') 2 where
  toFun v := (exists_isComponent q hΦg f hf hfrange v u).choose
  map_add' v w := by
    have hv := (exists_isComponent q hΦg f hf hfrange v u).choose_spec
    have hw := (exists_isComponent q hΦg f hf hfrange w u).choose_spec
    have hvw := (exists_isComponent q hΦg f hf hfrange (v + w) u).choose_spec
    refine IsComponent.unique hvw ?_
    rw [Submodule.coe_add, map_add]
    exact hv.add hw
  map_smul' c v := by
    have hv := (exists_isComponent q hΦg f hf hfrange v u).choose_spec
    have hcv := (exists_isComponent q hΦg f hf hfrange (c • v) u).choose_spec
    refine IsComponent.unique hcv ?_
    rw [Submodule.coe_smul, map_smul, RingHom.id_apply]
    exact hv.smul c

theorem isComponent_compF (u : ℤ_[q]ˣ) (v : VK q V) :
    IsComponent (f (v : V)) u (compF q hΦg f hf hfrange u v) :=
  (exists_isComponent q hΦg f hf hfrange v u).choose_spec

theorem compF_eq_of_toZMod_eq {u u' : ℤ_[q]ˣ}
    (huu' : PadicInt.toZMod (u : ℤ_[q]) = PadicInt.toZMod (u' : ℤ_[q])) (v : VK q V) :
    compF q hΦg f hf hfrange u v = compF q hΦg f hf hfrange u' v :=
  IsComponent.unique
    (IsComponentFn.of_toZMod_eq (mem_fixed_apply q hΦg f hf hfrange v) huu' (isComponent_compF q hΦg f hf hfrange u v))
    (isComponent_compF q hΦg f hf hfrange u' v)

theorem eq_zero_of_forall_compF_eq_zero (hfinj : Function.Injective f) (v : VK q V)
    (h0 : ∀ u : ℤ_[q]ˣ, compF q hΦg f hf hfrange u v = 0) : v = 0 := by
  have hy : f (v : V) = 0 := by
    refine CuspForm.IsAdelicLiftOf.eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule
      q hΦg (f (v : V)) (mem_span_apply q hΦg f hf hfrange v) (mem_fixed_apply q hΦg f hf hfrange v) (fun u h hh hp => ?_)
    have := isComponent_compF q hΦg f hf hfrange u v h hh hp
    rw [h0 u, CuspForm.coe_zero, SlashAction.zero_slash] at this
    exact this
  have : (v : V) = 0 := hfinj (by rw [hy, map_zero])
  exact Subtype.ext this

theorem coe_compF_gl2ReductionRep (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (u : ℤ_[q]ˣ)
    (γ : SL(2, ℤ)) (hγM : γ ∈ CongruenceSubgroup.Gamma M')
    (hγq : ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) =
      ((CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) *
          LocalNewvector.gl2ReductionHom q k *
          (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom
            (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))⁻¹ : CuspidalType.GL2 q) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) i j)
    (v : VK q V) :
    ⇑(compF q hΦg f hf hfrange u (gl2ReductionRep q V (gl2ReductionHom q k) v)) =
      (⇑(compF q hΦg f hf hfrange (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k)) v))
        ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  refine IsComponent.coe_eq (isComponent_compF q hΦg f hf hfrange u _) ?_
  intro h hh hp
  have hE := CuspForm.IsAdelicLiftOf.apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
    q hΦg (f (v : V)) (mem_span_apply q hΦg f hf hfrange v) (mem_fixed_apply q hΦg f hf hfrange v) k u γ hγM hγq
    (compF q hΦg f hf hfrange (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k)) v)
    (isComponent_compF q hΦg f hf hfrange _ v) h hh hp
  rw [gl2ReductionRep_gl2ReductionHom_apply, hf, toFn_padic_smul_apply, mul_assoc, ← map_mul]
  exact hE

end Comp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end Ws41.E4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped TensorProduct MatrixGroups ModularForm

noncomputable section

namespace Ws41
namespace E4

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup

section SlashCF

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

open ConjAct Pointwise in

def slashCF (g : GL (Fin 2) ℝ) (hg : toConjAct g⁻¹ • Γ = Γ) (F : CuspForm Γ k) : CuspForm Γ k where
  toFun := ⇑F ∣[k] g
  slash_action_eq' γ hγ := (CuspForm.translate F g).slash_action_eq' γ (by rw [hg]; exact hγ)
  holo' := (CuspForm.translate F g).holo'
  zero_at_cusps' hc := (CuspForm.translate F g).zero_at_cusps' (by rw [hg]; exact hc)

open ConjAct Pointwise in
@[scoped simp] theorem coe_slashCF (g : GL (Fin 2) ℝ) (hg : toConjAct g⁻¹ • Γ = Γ) (F : CuspForm Γ k) :
    ⇑(slashCF g hg F) = ⇑F ∣[k] g := rfl

open ConjAct Pointwise in

def slashLin [Γ.HasDetOne] (g : GL (Fin 2) ℝ) (hg : toConjAct g⁻¹ • Γ = Γ)
    (hdet : 0 < ((Matrix.GeneralLinearGroup.det g : ℝˣ) : ℝ)) : CuspForm Γ k →ₗ[ℂ] CuspForm Γ k where
  toFun := slashCF g hg
  map_add' F G := DFunLike.coe_injective <| by
    show ⇑(F + G) ∣[k] g = ⇑F ∣[k] g + ⇑G ∣[k] g
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c F := DFunLike.coe_injective <| by
    show ⇑(c • F) ∣[k] g = ⇑(c • slashCF g hg F)
    rw [CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, coe_slashCF, ModularForm.smul_slash,
      UpperHalfPlane.σ, if_pos hdet, ContinuousAlgEquiv.refl_apply]

open ConjAct Pointwise in
@[scoped simp] theorem coe_slashLin [Γ.HasDetOne] (g : GL (Fin 2) ℝ) (hg : toConjAct g⁻¹ • Γ = Γ)
    (hdet : 0 < ((Matrix.GeneralLinearGroup.det g : ℝˣ) : ℝ)) (F : CuspForm Γ k) :
    ⇑(slashLin g hg hdet F) = ⇑F ∣[k] g := rfl

end SlashCF
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section ConjElem

variable (q : ℕ) [Fact q.Prime]

theorem coe_SL_eq_mapGL (γ : SL(2, ℤ)) : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl

theorem coe_SL_GL_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := rfl

theorem SL_coe_GL_injective : Function.Injective fun γ : SL(2, ℤ) => (γ : GL (Fin 2) ℝ) := by
  intro a b h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simp only [coe_SL_GL_apply] at this
  exact_mod_cast this

theorem coe_SL_mul (x y : SL(2, ℤ)) : ((x * y : SL(2, ℤ)) : GL (Fin 2) ℝ) = (x : GL (Fin 2) ℝ) * (y : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) x y

theorem coe_SL_one : ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := map_one (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem coe_SL_inv (x : SL(2, ℤ)) : ((x⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (x : GL (Fin 2) ℝ)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) x

theorem val_conjElem (γ : SL(2, ℤ)) :
    ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ), (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) / q;
         (q : ℝ) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℝ), (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℝ)] := by
  rw [conjElem, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem heckeDiagMatrix_mul_conjElem (γ : SL(2, ℤ)) :
    ModularForm.heckeDiagMatrix q * conjElem q γ = (γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeDiagMatrix hq0, val_conjElem]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem conjElem_eq (γ : SL(2, ℤ)) :
    conjElem q γ = (ModularForm.heckeDiagMatrix q)⁻¹ * (γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, heckeDiagMatrix_mul_conjElem]

theorem conjElem_mul (a b : SL(2, ℤ)) : conjElem q (a * b) = conjElem q a * conjElem q b := by
  rw [conjElem_eq, conjElem_eq, conjElem_eq, coe_SL_mul]
  group

theorem conjElem_one : conjElem q 1 = 1 := by
  rw [conjElem_eq, coe_SL_one, mul_one, inv_mul_cancel]

theorem conjElem_inv (a : SL(2, ℤ)) : conjElem q a⁻¹ = (conjElem q a)⁻¹ := by
  rw [conjElem_eq, conjElem_eq, coe_SL_inv]
  group

theorem det_conjElem (γ : SL(2, ℤ)) : ((Matrix.GeneralLinearGroup.det (conjElem q γ) : ℝˣ) : ℝ) = 1 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hdet : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℝ) -
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_conjElem, Matrix.det_fin_two_of]
  have e : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) / q * ((q : ℝ) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℝ)) =
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℝ) := by
    field_simp
  rw [e, hdet]

theorem det_conjElem_pos (γ : SL(2, ℤ)) : 0 < ((Matrix.GeneralLinearGroup.det (conjElem q γ) : ℝˣ) : ℝ) := by
  rw [det_conjElem]; exact one_pos

theorem det_conjElem_inv_pos (γ : SL(2, ℤ)) : 0 < ((Matrix.GeneralLinearGroup.det (conjElem q γ)⁻¹ : ℝˣ) : ℝ) := by
  rw [map_inv, Units.val_inv_eq_inv_val, inv_pos]; exact det_conjElem_pos q γ

theorem coe_eq_conjElem_of_entries (γ γ' : SL(2, ℤ))
    (h00 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (h01 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    (h10 : (q : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (h11 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1) :
    ((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElem q γ := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [val_conjElem, coe_SL_GL_apply]
  fin_cases i <;> fin_cases j
  · simp [h00]
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    rw [h01]; push_cast; field_simp
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    rw [← h10]; push_cast; ring
  · simp [h11]

end ConjElem
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section LevelH

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

abbrev ΓH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (levelH q M')

abbrev SH : Type := CuspForm (ΓH q M') 2

include hqM'

theorem exists_mem_GammaH_coe_eq_conjElem (γ : SL(2, ℤ)) (hγ : γ ∈ Γfull q M') :
    ∃ γ' : SL(2, ℤ), γ' ∈ ΓH q M' ∧ ((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElem q γ := by
  obtain ⟨γ', h00, h01, h10, h11⟩ :=
    (CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq q M' hqM').1 ⟨γ, hγ⟩
  exact ⟨γ', γ'.2, coe_eq_conjElem_of_entries q γ γ' h00 h01 h10 h11⟩

theorem exists_mem_Gamma_conjElem_eq_coe (γ' : SL(2, ℤ)) (hγ' : γ' ∈ ΓH q M') :
    ∃ γ : SL(2, ℤ), γ ∈ Γfull q M' ∧ conjElem q γ = ((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  obtain ⟨γ, h00, h01, h10, h11⟩ :=
    (CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq q M' hqM').2.1 ⟨γ', hγ'⟩
  exact ⟨γ, γ.2, (coe_eq_conjElem_of_entries q γ γ' h00 h01 h10 h11).symm⟩

theorem conjElem_mul_mul_inv_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (x : GL (Fin 2) ℝ)
    (hx : x ∈ (ΓH q M' : Subgroup (GL (Fin 2) ℝ))) :
    conjElem q γ * x * (conjElem q γ)⁻¹ ∈ (ΓH q M' : Subgroup (GL (Fin 2) ℝ)) := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨g0, hg0, hconj⟩ := exists_mem_Gamma_conjElem_eq_coe q M' hqM' g hg
  have hmem : γ * g0 * γ⁻¹ ∈ Γfull q M' := by
    refine Subgroup.mem_inf.mpr ⟨(Gamma_normal q).conj_mem _ (Subgroup.mem_inf.mp hg0).1 γ, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ (Subgroup.mem_inf.mp hg0).2) (Subgroup.inv_mem _ hγ)
  obtain ⟨g', hg', hcoe⟩ := exists_mem_GammaH_coe_eq_conjElem q M' hqM' _ hmem
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ) g = conjElem q g0 from hconj.symm, ← conjElem_mul,
    ← conjElem_inv, ← conjElem_mul, ← hcoe]
  exact Subgroup.mem_map_of_mem _ hg'

open ConjAct Pointwise in

theorem toConjAct_conjElem_smul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    toConjAct (conjElem q γ) • (ΓH q M' : Subgroup (GL (Fin 2) ℝ)) = (ΓH q M' : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, toConjAct_smul, inv_inv]
  constructor
  · intro h
    have := conjElem_mul_mul_inv_mem q M' hqM' γ hγ _ h
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one] at this
  · intro h
    have := conjElem_mul_mul_inv_mem q M' hqM' γ⁻¹ (inv_mem hγ) x h
    rwa [conjElem_inv, inv_inv] at this

def Lop (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') : SH q M' →ₗ[ℂ] SH q M' :=
  slashLin (conjElem q γ)⁻¹ (by rw [inv_inv]; exact toConjAct_conjElem_smul q M' hqM' γ hγ)
    (det_conjElem_inv_pos q γ)

theorem coe_Lop (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (F : SH q M') :
    ⇑(Lop q M' hqM' γ hγ F) = ⇑F ∣[(2 : ℤ)] (conjElem q γ)⁻¹ := rfl

theorem exists_coe_eq_inv_mul_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(ΓH q M')) :
    ∃ δ' : SL(2, ℤ), δ' ∈ ΓH q M' ∧
      ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = (conjElem q γ)⁻¹ * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * conjElem q γ := by
  have h := conjElem_mul_mul_inv_mem q M' hqM' γ⁻¹ (inv_mem hγ) _ (Subgroup.mem_map_of_mem _ δ.2)
  rw [conjElem_inv, inv_inv] at h
  obtain ⟨δ', hδ', he⟩ := Subgroup.mem_map.mp h
  exact ⟨δ', hδ', he⟩

def cFun (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(ΓH q M')) : ↥(ΓH q M') :=
  ⟨(exists_coe_eq_inv_mul_mul q M' hqM' γ hγ δ).choose, (exists_coe_eq_inv_mul_mul q M' hqM' γ hγ δ).choose_spec.1⟩

theorem coe_cFun (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(ΓH q M')) :
    (((cFun q M' hqM' γ hγ δ : ↥(ΓH q M')) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (conjElem q γ)⁻¹ * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * conjElem q γ :=
  (exists_coe_eq_inv_mul_mul q M' hqM' γ hγ δ).choose_spec.2

def cHom (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') : ↥(ΓH q M') →* ↥(ΓH q M') where
  toFun := cFun q M' hqM' γ hγ
  map_one' := by
    apply Subtype.ext
    apply SL_coe_GL_injective
    show (((cFun q M' hqM' γ hγ 1 : ↥(ΓH q M')) : SL(2, ℤ)) : GL (Fin 2) ℝ) = ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ)
    rw [coe_cFun, OneMemClass.coe_one, coe_SL_one, mul_one, inv_mul_cancel]
  map_mul' a b := by
    apply Subtype.ext
    apply SL_coe_GL_injective
    show (((cFun q M' hqM' γ hγ (a * b) : ↥(ΓH q M')) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((((cFun q M' hqM' γ hγ a : ↥(ΓH q M')) : SL(2, ℤ)) * ((cFun q M' hqM' γ hγ b : ↥(ΓH q M')) : SL(2, ℤ)) :
        SL(2, ℤ)) : GL (Fin 2) ℝ)
    rw [coe_SL_mul, coe_cFun, coe_cFun, coe_cFun, Subgroup.coe_mul, coe_SL_mul]
    group

theorem coe_cHom (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(ΓH q M')) :
    (((cHom q M' hqM' γ hγ δ : ↥(ΓH q M')) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (conjElem q γ)⁻¹ * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * ((conjElem q γ)⁻¹)⁻¹ := by
  rw [inv_inv]
  exact coe_cFun q M' hqM' γ hγ δ

theorem periodOf_Lop (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (δ : ↥(ΓH q M')) (F : SH q M') :
    periodOf (ΓH q M') δ (Lop q M' hqM' γ hγ F) = periodOf (ΓH q M') (cHom q M' hqM' γ hγ δ) F := by
  rw [← periodMapOf_apply_eq_periodOf, ← periodMapOf_apply_eq_periodOf,
    ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash (q ^ 2 * M') (levelH q M') (conjElem q γ)⁻¹
      (det_conjElem_inv_pos q γ) (cHom q M' hqM' γ hγ) (coe_cHom q M' hqM' γ hγ) F (Lop q M' hqM' γ hγ F)
      (coe_Lop q M' hqM' γ hγ F)]
  rfl

theorem dualMap_Lop_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∀ v ∈ periodLatticeOf (ΓH q M'), (Lop q M' hqM' γ hγ).dualMap v ∈ periodLatticeOf (ΓH q M') := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    have : (Lop q M' hqM' γ hγ).dualMap (periodOf _ δ) = periodOf _ (cHom q M' hqM' γ hγ δ) :=
      LinearMap.ext fun F => by rw [LinearMap.dualMap_apply, periodOf_Lop]
    rw [this]
    exact periodOf_mem_periodLatticeOf _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

omit hqM' in

theorem slash_eq_slash_of_mul_inv_mem (F : SH q M') (A B : GL (Fin 2) ℝ)
    (h : A * B⁻¹ ∈ (ΓH q M' : Subgroup (GL (Fin 2) ℝ))) : ⇑F ∣[(2 : ℤ)] A = ⇑F ∣[(2 : ℤ)] B := by
  have e : A = A * B⁻¹ * B := by rw [inv_mul_cancel_right]
  rw [e, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq F _ h]

end LevelH
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Transport

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

def Ldelta : CuspForm (Γfull q M') 2 ≃ₗ[ℂ] SH q M' :=
  (CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq q M' hqM').2.2.choose

theorem coe_Ldelta (F : CuspForm (Γfull q M') 2) :
    ⇑(Ldelta q M' hqM' F) = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q :=
  (CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq q M' hqM').2.2.choose_spec.1 F

theorem slash_SL_slash_heckeDiagMatrix (F : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    (F ∣[(2 : ℤ)] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q =
      (F ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∣[(2 : ℤ)] conjElem q γ := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, heckeDiagMatrix_mul_conjElem]

end Transport
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Diamond

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ} {k : ℤ}

theorem mul_inv_mem_GammaH_of_mem (ρ σ : Gamma0 N)
    (h : CohCarrier.gamma0Units N ρ * (CohCarrier.gamma0Units N σ)⁻¹ ∈ H) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH N H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(ρ * σ⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹, (ρ * σ⁻¹).2⟩ : Gamma0 N) = ρ * σ⁻¹ := rfl
  rw [e1, map_mul, map_inv]
  exact h

theorem slash_mapGL_eq_of_mul_inv_mem {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (ρ σ : Gamma0 N) (h : CohCarrier.gamma0Units N ρ * (CohCarrier.gamma0Units N σ)⁻¹ ∈ H) (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) := by
  have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_GammaH_of_mem ρ σ h))]

theorem coe_diamondLinH_eq_slash_of_mem (a : (ZMod N)ˣ) (σ : Gamma0 N)
    (hσ : CohCarrier.gamma0Units N σ * a⁻¹ ∈ H) (F : CuspForm (CohCarrier.GammaH N H) k) :
    ⇑(CuspForm.diamondLinH k a F) = ⇑F ∣[k] ((σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD N H k)]
  have := slash_mapGL_eq_of_mul_inv_mem (k := k) (fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ)
    (CuspForm.gammaLift N a) σ (by
      rw [CuspForm.gamma0Units_gammaLift]
      have : a * (CohCarrier.gamma0Units N σ)⁻¹ = (CohCarrier.gamma0Units N σ * a⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hσ) 1
  rwa [mul_one, mul_one] at this

theorem diamondLinH_eq_of_mul_inv_mem (a b : (ZMod N)ˣ) (h : a * b⁻¹ ∈ H)
    (F : CuspForm (CohCarrier.GammaH N H) k) :
    CuspForm.diamondLinH k a F = CuspForm.diamondLinH k b F := by
  apply DFunLike.coe_injective
  rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD N H k) b]
  exact coe_diamondLinH_eq_slash_of_mem a (CuspForm.gammaLift N b)
    (by rw [CuspForm.gamma0Units_gammaLift]; have := inv_mem h; rwa [mul_inv_rev, inv_inv] at this) F

theorem diamondLinH_diamondLinH (a b : (ZMod N)ˣ) (F : CuspForm (CohCarrier.GammaH N H) k) :
    CuspForm.diamondLinH k a (CuspForm.diamondLinH k b F) = CuspForm.diamondLinH k (b * a) F := by
  apply DFunLike.coe_injective
  rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD N H k) a,
    CuspForm.coe_diamondLinH_apply k (CuspForm.stableD N H k) b, ← SlashAction.slash_mul, ← map_mul,
    CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD N H k) (b * a)
      (CuspForm.gammaLift N b * CuspForm.gammaLift N a)
      (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift])]
  rfl

theorem diamondLinH_comm (a b : (ZMod N)ˣ) (F : CuspForm (CohCarrier.GammaH N H) k) :
    CuspForm.diamondLinH k a (CuspForm.diamondLinH k b F) = CuspForm.diamondLinH k b (CuspForm.diamondLinH k a F) := by
  rw [diamondLinH_diamondLinH, diamondLinH_diamondLinH, mul_comm]

theorem diamondLinH_one (F : CuspForm (CohCarrier.GammaH N H) k) : CuspForm.diamondLinH k 1 F = F := by
  apply DFunLike.coe_injective
  rw [CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD N H k) 1 1 (map_one _)]
  show ⇑F ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑F
  rw [map_one, SlashAction.slash_one]

theorem diamondLinH_inv_diamondLinH (a : (ZMod N)ˣ) (F : CuspForm (CohCarrier.GammaH N H) k) :
    CuspForm.diamondLinH k a⁻¹ (CuspForm.diamondLinH k a F) = F := by
  rw [diamondLinH_diamondLinH, mul_inv_cancel, diamondLinH_one]

theorem diamondLinH_injective (a : (ZMod N)ˣ) :
    Function.Injective (CuspForm.diamondLinH k a : CuspForm (CohCarrier.GammaH N H) k → _) := by
  intro F G h
  rw [← diamondLinH_inv_diamondLinH a F, ← diamondLinH_inv_diamondLinH a G, h]

end Diamond
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end Ws41.E4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false

open scoped MatrixGroups

namespace Ws41
namespace E4Kit

theorem det_map {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : GL n R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.map_det, RingHom.mapMatrix_apply]
  rfl

theorem det_diagOneElem (q : ℕ) [Fact q.Prime] (d : (ZMod q)ˣ) :
    Matrix.GeneralLinearGroup.det (ModularCurve.FullLevel.diagOneElem q d) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ModularCurve.FullLevel.coe_diagOneElem, Matrix.det_fin_two_of]
  ring

theorem det_diagElem (q : ℕ) [Fact q.Prime] (a : (ZMod q)ˣ) :
    Matrix.GeneralLinearGroup.det (CuspidalType.diagElem q a) = a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    show ((CuspidalType.diagElem q a : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(a : ZMod q), 0; 0, 1]
      from rfl, Matrix.det_fin_two_of]
  ring

theorem det_gl2ReductionHom (q : ℕ) [Fact q.Prime] (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) :
    Matrix.GeneralLinearGroup.det (LocalNewvector.gl2ReductionHom q k) =
      Units.map PadicInt.toZMod.toMonoidHom (Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k)) :=
  det_map _ _

theorem coe_redQ_apply (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((ModularCurve.FullLevel.redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j
      = (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) := rfl

theorem redQ_eq_of_forall_entry (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) (m : CuspidalType.GL2 q)
    (h : ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) = (m : Matrix (Fin 2) (Fin 2) (ZMod q)) i j) :
    ModularCurve.FullLevel.redQ q γ = m :=
  Matrix.GeneralLinearGroup.ext fun i j => by rw [coe_redQ_apply]; exact h i j

theorem forall_entry_of_redQ_eq (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) (m : CuspidalType.GL2 q)
    (h : ModularCurve.FullLevel.redQ q γ = m) :
    ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) = (m : Matrix (Fin 2) (Fin 2) (ZMod q)) i j :=
  fun i j => by rw [← coe_redQ_apply, h]

theorem redQ_eq_iff_forall_entry (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) (m : CuspidalType.GL2 q) :
    ModularCurve.FullLevel.redQ q γ = m ↔
      ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) = (m : Matrix (Fin 2) (Fin 2) (ZMod q)) i j :=
  ⟨forall_entry_of_redQ_eq q γ m, redQ_eq_of_forall_entry q γ m⟩

theorem redQ_apply (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) :
    ModularCurve.FullLevel.redQ q γ =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) := rfl

theorem coe_redQ (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) :
    ((ModularCurve.FullLevel.redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) :=
  rfl

theorem redQ_eq_one_iff_mem_Gamma (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) :
    ModularCurve.FullLevel.redQ q γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma q := by
  rw [CongruenceSubgroup.Gamma_mem']
  constructor
  · intro h
    apply Subtype.ext
    have := congrArg (fun x : CuspidalType.GL2 q => (x : Matrix (Fin 2) (Fin 2) (ZMod q))) h
    simpa [coe_redQ] using this
  · intro h
    rw [redQ_apply, h, map_one]

theorem exists_mem_Gamma_redQ_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (m : CuspidalType.GL2 q) (hm : Matrix.GeneralLinearGroup.det m = 1) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma M' ∧ ModularCurve.FullLevel.redQ q γ = m := by
  have hdet : (m : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hm, Units.val_one]
  obtain ⟨γ, hγ, hmap⟩ :=
    (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1 ⟨(m : Matrix (Fin 2) (Fin 2) (ZMod q)), hdet⟩
  refine ⟨γ, hγ, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [coe_redQ, hmap]

theorem toZMod_natCast (q : ℕ) [Fact q.Prime] (ℓ : ℕ) : PadicInt.toZMod ((ℓ : ℤ_[q])) = (ℓ : ZMod q) :=
  map_natCast _ _

theorem exists_unit_coe_eq_natCast_of_not_dvd (q : ℕ) [Fact q.Prime] {ℓ : ℕ} (hℓ : ¬ q ∣ ℓ) :
    ∃ u : ℤ_[q]ˣ, (u : ℤ_[q]) = ℓ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hu : IsUnit ((ℓ : ℤ_[q])) := by
    by_contra hna
    have hmem : (ℓ : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at hmem
    exact hℓ hmem
  exact ⟨hu.unit, hu.unit_spec⟩

theorem unitsMap_unitOfCoprime {n m : ℕ} [NeZero m] (h : n ∣ m) (ℓ : ℕ) (h₁ : ℓ.Coprime m) (h₂ : ℓ.Coprime n) :
    ZMod.unitsMap h (ZMod.unitOfCoprime ℓ h₁) = ZMod.unitOfCoprime ℓ h₂ := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]

end Ws41.E4Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false

open scoped MatrixGroups

namespace Ws41
namespace E4Kit

section Diag
variable (q : ℕ) [Fact q.Prime]

theorem coe_diagElem (a : (ZMod q)ˣ) :
    ((CuspidalType.diagElem q a : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(a : ZMod q), 0; 0, 1] :=
  rfl

theorem diagOneElem_mul (a b : (ZMod q)ˣ) :
    ModularCurve.FullLevel.diagOneElem q (a * b) =
      ModularCurve.FullLevel.diagOneElem q a * ModularCurve.FullLevel.diagOneElem q b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, ModularCurve.FullLevel.coe_diagOneElem, ModularCurve.FullLevel.coe_diagOneElem,
    ModularCurve.FullLevel.coe_diagOneElem]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagOneElem_one : ModularCurve.FullLevel.diagOneElem q 1 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [ModularCurve.FullLevel.coe_diagOneElem, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOneElem_inv (d : (ZMod q)ˣ) :
    (ModularCurve.FullLevel.diagOneElem q d)⁻¹ = ModularCurve.FullLevel.diagOneElem q d⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← diagOneElem_mul, mul_inv_cancel, diagOneElem_one])

theorem diagElem_mul (a b : (ZMod q)ˣ) :
    CuspidalType.diagElem q (a * b) = CuspidalType.diagElem q a * CuspidalType.diagElem q b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_diagElem, coe_diagElem, coe_diagElem]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagElem_one : CuspidalType.diagElem q 1 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_diagElem, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

theorem diagElem_inv (a : (ZMod q)ˣ) :
    (CuspidalType.diagElem q a)⁻¹ = CuspidalType.diagElem q a⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← diagElem_mul, mul_inv_cancel, diagElem_one])

theorem diagElem_mul_diagOneElem_comm (a b : (ZMod q)ˣ) :
    CuspidalType.diagElem q a * ModularCurve.FullLevel.diagOneElem q b =
      ModularCurve.FullLevel.diagOneElem q b * CuspidalType.diagElem q a := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, coe_diagElem, ModularCurve.FullLevel.coe_diagOneElem]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_diagElem_mul_diagOneElem (a b : (ZMod q)ˣ) :
    ((CuspidalType.diagElem q a * ModularCurve.FullLevel.diagOneElem q b : CuspidalType.GL2 q) :
      Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(a : ZMod q), 0; 0, (b : ZMod q)] := by
  rw [Units.val_mul, coe_diagElem, ModularCurve.FullLevel.coe_diagOneElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_redQ (γ : SL(2, ℤ)) : Matrix.GeneralLinearGroup.det (ModularCurve.FullLevel.redQ q γ) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ).2

end Diag
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Flat
variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

omit [NeZero M'] in
theorem coe_unitsMap_gamma0Units (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M')) :
    ((ZMod.unitsMap (ModularCurve.FullLevel.dvd_sq_mul q M') (CohCarrier.gamma0Units (q ^ 2 * M') ⟨σ, hσ⟩) :
        (ZMod q)ˣ) : ZMod q) = (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q) := by
  rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units]
  show ZMod.castHom _ _ ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (q ^ 2 * M'))) = _
  rw [ZMod.castHom_apply, ZMod.cast_intCast (ModularCurve.FullLevel.dvd_sq_mul q M')]

omit [NeZero M'] in
theorem coe_unitsMap_gamma0Units_inv (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M')) :
    (((ZMod.unitsMap (ModularCurve.FullLevel.dvd_sq_mul q M') (CohCarrier.gamma0Units (q ^ 2 * M') ⟨σ, hσ⟩))⁻¹ :
        (ZMod q)ˣ) : ZMod q) = (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) := by
  rw [← map_inv, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe]
  show ZMod.castHom _ _ ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod (q ^ 2 * M'))) = _
  rw [ZMod.castHom_apply, ZMod.cast_intCast (ModularCurve.FullLevel.dvd_sq_mul q M')]

theorem exists_conjElem_eq_of_mem_Gamma0 (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M')) :
    ∃ τ : SL(2, ℤ), ModularCurve.FullLevel.conjElem q τ = ((σ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∧
      τ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.redQ q τ =
        CuspidalType.diagElem q (ZMod.unitsMap (ModularCurve.FullLevel.dvd_sq_mul q M')
            (CohCarrier.gamma0Units (q ^ 2 * M') ⟨σ, hσ⟩))⁻¹ *
          ModularCurve.FullLevel.diagOneElem q (ZMod.unitsMap (ModularCurve.FullLevel.dvd_sq_mul q M')
            (CohCarrier.gamma0Units (q ^ 2 * M') ⟨σ, hσ⟩)) := by
  have hq : q.Prime := Fact.out
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set a : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe σ; rw [Matrix.det_fin_two] at this; exact this
  have hcdvd : ((q ^ 2 * M' : ℕ) : ℤ) ∣ c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact CongruenceSubgroup.Gamma0_mem.mp hσ
  obtain ⟨k, hk⟩ := hcdvd
  have hτdet : Matrix.det !![a, (q : ℤ) * b; ((q * M' : ℕ) : ℤ) * k, d] = 1 := by
    rw [Matrix.det_fin_two_of, ← hdet, hk]; push_cast; ring
  refine ⟨⟨!![a, (q : ℤ) * b; ((q * M' : ℕ) : ℤ) * k, d], hτdet⟩, ?_, ?_, ?_⟩
  ·
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Ws41.E4.val_conjElem, Ws41.E4.coe_SL_GL_apply]
    fin_cases i <;> fin_cases j
    · rfl
    · show (((q : ℤ) * b : ℤ) : ℝ) / q = (b : ℝ); push_cast; field_simp
    · show (q : ℝ) * ((((q * M' : ℕ) : ℤ) * k : ℤ) : ℝ) = (c : ℝ); rw [hk]; push_cast; ring
    · rfl
  ·
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((((q * M' : ℕ) : ℤ) * k : ℤ) : ZMod M') = 0
    push_cast; simp
  ·
    refine redQ_eq_of_forall_entry q _ _ fun i j => ?_
    rw [coe_diagElem_mul_diagOneElem, coe_unitsMap_gamma0Units, coe_unitsMap_gamma0Units_inv]
    fin_cases i <;> fin_cases j
    · rfl
    · show ((((q : ℤ) * b : ℤ)) : ZMod q) = 0; push_cast; simp
    · show ((((q * M' : ℕ) : ℤ) * k : ℤ) : ZMod q) = 0; push_cast; simp
    · rfl

end Flat
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Key
variable (q : ℕ) [Fact q.Prime]

theorem key_identity (x : CuspidalType.GL2 q) (e : (ZMod q)ˣ) :
    (CuspidalType.diagElem q e⁻¹ * x * (CuspidalType.diagElem q (e⁻¹ * Matrix.GeneralLinearGroup.det x))⁻¹)⁻¹ *
      (CuspidalType.diagElem q e⁻¹ * ModularCurve.FullLevel.diagOneElem q e) *
      (ModularCurve.FullLevel.diagOneElem q (e * (Matrix.GeneralLinearGroup.det x)⁻¹)⁻¹ *
          (ModularCurve.FullLevel.diagOneElem q (Matrix.GeneralLinearGroup.det x)⁻¹ * x) *
        (ModularCurve.FullLevel.diagOneElem q (e * (Matrix.GeneralLinearGroup.det x)⁻¹)⁻¹)⁻¹) *
      (CuspidalType.diagElem q (e * (Matrix.GeneralLinearGroup.det x)⁻¹)⁻¹ *
          ModularCurve.FullLevel.diagOneElem q (e * (Matrix.GeneralLinearGroup.det x)⁻¹))⁻¹ = 1 := by
  set D := CuspidalType.diagElem q with hD
  set O := ModularCurve.FullLevel.diagOneElem q with hO
  set δ := Matrix.GeneralLinearGroup.det x with hδ
  have hD_mul : ∀ a b, D (a * b) = D a * D b := diagElem_mul q
  have hO_mul : ∀ a b, O (a * b) = O a * O b := diagOneElem_mul q
  have hD_inv : ∀ a, (D a)⁻¹ = D a⁻¹ := diagElem_inv q
  have hO_inv : ∀ a, (O a)⁻¹ = O a⁻¹ := diagOneElem_inv q
  have hD_one : D 1 = 1 := diagElem_one q
  have hO_one : O 1 = 1 := diagOneElem_one q
  have hed : e⁻¹ * δ = (e * δ⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
  rw [hed]
  set u := e * δ⁻¹ with hu
  have heud : e * u⁻¹ * δ⁻¹ = 1 := by
    rw [hu, mul_inv_rev, inv_inv, mul_comm δ e⁻¹, ← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel]
  clear_value u δ D O
  have T1 : (D e⁻¹ * x * (D u⁻¹)⁻¹)⁻¹ = D u⁻¹ * x⁻¹ * D e := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hD_inv, inv_inv, mul_assoc]
  have T3 : O u⁻¹ * (O δ⁻¹ * x) * (O u⁻¹)⁻¹ = O u⁻¹ * O δ⁻¹ * x * O u := by
    simp only [hO_inv, inv_inv, mul_assoc]
  have T4 : (D u⁻¹ * O u)⁻¹ = O u⁻¹ * D u := by rw [mul_inv_rev, hO_inv, hD_inv, inv_inv]
  rw [T1, T3, T4]
  have h12 : ∀ y : CuspidalType.GL2 q, D e * (D e⁻¹ * y) = y := fun y => by
    rw [← mul_assoc, ← hD_mul, mul_inv_cancel, hD_one, one_mul]
  have h3 : ∀ y : CuspidalType.GL2 q, O e * (O u⁻¹ * (O δ⁻¹ * y)) = y := fun y => by
    rw [← mul_assoc, ← mul_assoc, ← hO_mul, ← hO_mul, heud, hO_one, one_mul]
  have h4 : ∀ y : CuspidalType.GL2 q, O u * (O u⁻¹ * y) = y := fun y => by
    rw [← mul_assoc, ← hO_mul, mul_inv_cancel, hO_one, one_mul]
  simp only [mul_assoc]
  rw [h12, h3, inv_mul_cancel_left, h4, ← hD_mul, inv_mul_cancel, hD_one]

end Key
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end Ws41.E4Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped TensorProduct MatrixGroups ModularForm

noncomputable section

namespace Ws41
namespace E4

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

section Units

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

scoped instance neZero_sq_mul : NeZero (q ^ 2 * M') :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩

def nLift (a : (ZMod q)ˣ) : (ZMod (q ^ 2 * M'))ˣ :=
  (ZMod.unitsMap_surjective (dvd_sq_mul q M') a).choose

theorem unitsMap_nLift (a : (ZMod q)ˣ) : ZMod.unitsMap (dvd_sq_mul q M') (nLift q M' a) = a :=
  (ZMod.unitsMap_surjective (dvd_sq_mul q M') a).choose_spec

variable {q M'} in
theorem mul_inv_mem_levelH_iff (a b : (ZMod (q ^ 2 * M'))ˣ) :
    a * b⁻¹ ∈ levelH q M' ↔ ZMod.unitsMap (dvd_sq_mul q M') a = ZMod.unitsMap (dvd_sq_mul q M') b := by
  rw [mem_levelH_iff, map_mul, map_inv, mul_inv_eq_one]

theorem unitsMap_unitOfCoprime {n m : ℕ} [NeZero m] (h : n ∣ m) (ℓ : ℕ) (h₁ : ℓ.Coprime m) (h₂ : ℓ.Coprime n) :
    ZMod.unitsMap h (ZMod.unitOfCoprime ℓ h₁) = ZMod.unitOfCoprime ℓ h₂ := by
  refine Units.ext ?_
  rw [ZMod.unitsMap_def, Units.coe_map, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe,
    map_natCast]

theorem toZMod_natCast (ℓ : ℕ) : PadicInt.toZMod ((ℓ : ℤ_[q])) = (ℓ : ZMod q) := map_natCast _ ℓ

theorem exists_unit_coe_eq_natCast_of_not_dvd {ℓ : ℕ} (hℓ : ¬ q ∣ ℓ) : ∃ u : ℤ_[q]ˣ, (u : ℤ_[q]) = ℓ := by
  have hu : IsUnit (ℓ : ℤ_[q]) := by
    by_contra hna
    have hmem : (ℓ : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, toZMod_natCast, ZMod.natCast_eq_zero_iff] at hmem
    exact hℓ hmem
  exact ⟨hu.unit, hu.unit_spec⟩

end Units
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Assembly

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
  [Algebra ℤ_[lam] ℂ]
  {g : CuspForm (Gamma0 (q ^ 2 * M')) 2} {Φ : 𝔸GL → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
  {V : Type} [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
  (f : V →ₗ[ℂ] AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
  (hfrange : LinearMap.range f =
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))

abbrev TJ : Type := TateModule lam (jacComp q M')

abbrev TT : Type := TateModule lam (Jac q M')

def Gcomp (e : (ZMod q)ˣ) : VK q V →ₗ[ℂ] SH q M' :=
  (CuspForm.diamondLinH 2 (nLift q M' e)) ∘ₗ (Ldelta q M' hqM').toLinearMap ∘ₗ
    compF q hΦg f hf hfrange (unitLift q e⁻¹)

theorem Gcomp_apply (e : (ZMod q)ˣ) (v : VK q V) :
    Gcomp q M' hqM' hΦg f hf hfrange e v =
      CuspForm.diamondLinH 2 (nLift q M' e) (Ldelta q M' hqM' (compF q hΦg f hf hfrange (unitLift q e⁻¹) v)) := rfl

def compDual (ζ : Idx q) :
    Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TJ q M' lam) →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TT q M' lam) :=
  ((tateMap lam (evalHom q M' ζ)).baseChange ℂ).dualMap

theorem compDual_apply (ζ : Idx q) (φ : Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TJ q M' lam)) (w : ℂ ⊗[ℤ_[lam]] TT q M' lam) :
    compDual q M' lam ζ φ w = φ (((tateMap lam (evalHom q M' ζ)).baseChange ℂ) w) := rfl

variable (ζ₀ : Idx q) (Ψ : SH q M' →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TJ q M' lam))

def psi : VK q V →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TT q M' lam) :=
  ∑ ζ : Idx q, compDual q M' lam ζ ∘ₗ Ψ ∘ₗ Gcomp q M' hqM' hΦg f hf hfrange ((idxEquiv ζ₀).symm ζ)

theorem psi_apply (v : VK q V) :
    psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ v =
      ∑ ζ : Idx q, compDual q M' lam ζ (Ψ (Gcomp q M' hqM' hΦg f hf hfrange ((idxEquiv ζ₀).symm ζ) v)) := by
  simp only [psi, LinearMap.sum_apply, LinearMap.comp_apply]

theorem dualMap_baseChange_psi (A : TT q M' lam →ₗ[ℤ_[lam]] TT q M' lam) (Aζ : Idx q → (TJ q M' lam →ₗ[ℤ_[lam]] TJ q M' lam))
    (s : Idx q ≃ Idx q)
    (hA : ∀ ζ, tateMap lam (evalHom q M' ζ) ∘ₗ A = Aζ ζ ∘ₗ tateMap lam (evalHom q M' (s ζ))) (v : VK q V) :
    (A.baseChange ℂ).dualMap (psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ v) =
      ∑ ζ : Idx q, compDual q M' lam (s ζ)
        (((Aζ ζ).baseChange ℂ).dualMap (Ψ (Gcomp q M' hqM' hΦg f hf hfrange ((idxEquiv ζ₀).symm ζ) v))) := by
  rw [psi_apply, map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  refine LinearMap.ext fun w => ?_
  simp only [compDual_apply, LinearMap.dualMap_apply]
  congr 1
  have hc : (tateMap lam (evalHom q M' ζ)).baseChange ℂ ∘ₗ A.baseChange ℂ =
      (Aζ ζ).baseChange ℂ ∘ₗ (tateMap lam (evalHom q M' (s ζ))).baseChange ℂ := by
    rw [← LinearMap.baseChange_comp, hA, LinearMap.baseChange_comp]
  exact LinearMap.congr_fun hc w

theorem sum_compDual_equiv (s : Idx q ≃ Idx q) (X : Idx q → Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TJ q M' lam)) :
    ∑ ζ : Idx q, compDual q M' lam (s ζ) (X ζ) = ∑ ζ : Idx q, compDual q M' lam ζ (X (s.symm ζ)) := by
  rw [← Equiv.sum_comp s (fun ζ => compDual q M' lam ζ (X (s.symm ζ)))]
  simp only [Equiv.symm_apply_apply]

def powEquiv (d : (ZMod q)ˣ) : Idx q ≃ Idx q where
  toFun ζ := ζ.pow d
  invFun ζ := ζ.pow d⁻¹
  left_inv ζ := Idx.pow_pow_inv ζ d
  right_inv ζ := Idx.pow_inv_pow ζ d

@[scoped simp] theorem powEquiv_apply (d : (ZMod q)ˣ) (ζ : Idx q) : powEquiv q d ζ = ζ.pow d := rfl
@[scoped simp] theorem powEquiv_symm_apply (d : (ZMod q)ˣ) (ζ : Idx q) : (powEquiv q d).symm ζ = ζ.pow d⁻¹ := rfl

theorem tateMap_comp (A B : jacComp q M' →+ jacComp q M') :
    tateMap lam (A.comp B) = tateMap lam A ∘ₗ tateMap lam B :=
  LinearMap.ext fun x => tateMap_comp_apply B A x

theorem evalMap_comp_tateGL2_redQ (hGL : GL2Laws q M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ζ : Idx q) :
    tateMap lam (evalHom q M' ζ) ∘ₗ (tateGL2 q M' lam (redQ q γ) : TT q M' lam →ₗ[ℤ_[lam]] TT q M' lam) =
      tateMap lam (levelOp q M' ζ γ⁻¹) ∘ₗ tateMap lam (evalHom q M' ζ) :=
  LinearMap.ext fun x => tateJacEquiv_tateGL2_redQ q M' lam hGL γ hγ x ζ

theorem evalMap_comp_tateGL2_diagOneElem (hGL : GL2Laws q M') (d : (ZMod q)ˣ) (ζ : Idx q) :
    tateMap lam (evalHom q M' ζ) ∘ₗ (tateGL2 q M' lam (diagOneElem q d) : TT q M' lam →ₗ[ℤ_[lam]] TT q M' lam) =
      tateMap lam (evalHom q M' (ζ.pow d⁻¹)) :=
  LinearMap.ext fun x => tateJacEquiv_tateGL2_diagOneElem q M' lam hGL d x ζ

theorem evalMap_comp_tateGL2_redQ_mul_diagOneElem (hGL : GL2Laws q M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (d : (ZMod q)ˣ) (ζ : Idx q) :
    tateMap lam (evalHom q M' ζ) ∘ₗ
        (tateGL2 q M' lam (redQ q γ * diagOneElem q d) : TT q M' lam →ₗ[ℤ_[lam]] TT q M' lam) =
      tateMap lam (levelOp q M' ζ γ⁻¹) ∘ₗ tateMap lam (evalHom q M' ((powEquiv q d).symm ζ)) := by
  rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, evalMap_comp_tateGL2_redQ q M' lam hGL γ hγ,
    LinearMap.comp_assoc, evalMap_comp_tateGL2_diagOneElem q M' lam hGL, powEquiv_symm_apply]

theorem evalMap_comp_tateHecke (hHC : HeckeGenCommute q M') (ℓ : Nat.Primes) (hℓqM : ¬ (ℓ : ℕ) ∣ q * M')
    (hq : (ℓ : ℕ).Coprime q) (hqM : (ℓ : ℕ).Coprime (q ^ 2 * M')) (ζ : Idx q) :
    tateMap lam (evalHom q M' ζ) ∘ₗ
        (tateHecke q M' lam (ModularCurve.heckeGen ℓ) : TT q M' lam →ₗ[ℤ_[lam]] TT q M' lam) =
      (tateMap lam (ModularCurve.diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹) ∘ₗ
        tateMap lam (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
          ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ)) ∘ₗ
        tateMap lam (evalHom q M' ((powEquiv q (ZMod.unitOfCoprime ℓ hq)).symm ζ)) := by
  rw [← tateMap_comp]
  exact LinearMap.ext fun x => tateJacEquiv_tateHecke_heckeGen q M' lam hHC ℓ hℓqM hq hqM x ζ

def inclMap (ζ : Idx q) : TJ q M' lam →ₗ[ℤ_[lam]] TT q M' lam :=
  (tateJacEquiv q M' lam).symm.toLinearMap ∘ₗ LinearMap.single ℤ_[lam] (fun _ : Idx q => TJ q M' lam) ζ

theorem tateJacEquiv_inclMap (ζ : Idx q) (y : TJ q M' lam) :
    tateJacEquiv q M' lam (inclMap q M' lam ζ y) = Pi.single ζ y := by
  show tateJacEquiv q M' lam ((tateJacEquiv q M' lam).symm
    (LinearMap.single ℤ_[lam] (fun _ : Idx q => TJ q M' lam) ζ y)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem evalMap_inclMap_same (ζ : Idx q) (y : TJ q M' lam) :
    tateMap lam (evalHom q M' ζ) (inclMap q M' lam ζ y) = y := by
  rw [← tateJacEquiv_apply, tateJacEquiv_inclMap]
  simp

theorem evalMap_inclMap_ne {ζ ζ' : Idx q} (h : ζ' ≠ ζ) (y : TJ q M' lam) :
    tateMap lam (evalHom q M' ζ') (inclMap q M' lam ζ y) = 0 := by
  rw [← tateJacEquiv_apply, tateJacEquiv_inclMap]
  simp [h]

theorem evalMap_comp_inclMap_same (ζ : Idx q) :
    tateMap lam (evalHom q M' ζ) ∘ₗ inclMap q M' lam ζ = LinearMap.id :=
  LinearMap.ext fun y => evalMap_inclMap_same q M' lam ζ y

theorem evalMap_comp_inclMap_ne {ζ ζ' : Idx q} (h : ζ' ≠ ζ) :
    tateMap lam (evalHom q M' ζ') ∘ₗ inclMap q M' lam ζ = 0 :=
  LinearMap.ext fun y => evalMap_inclMap_ne q M' lam h y

include hf hfrange in
set_option maxHeartbeats 8000000 in

theorem psi_injective (hΨ : Function.Injective Ψ) (hfinj : Function.Injective f) :
    Function.Injective (psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv

  have hζ : ∀ ζ : Idx q, Ψ (Gcomp q M' hqM' hΦg f hf hfrange ((idxEquiv ζ₀).symm ζ) v) = 0 := by
    intro ζ
    refine LinearMap.ext fun w => ?_
    have h := LinearMap.congr_fun hv (((inclMap q M' lam ζ).baseChange ℂ) w)
    rw [psi_apply, LinearMap.sum_apply, LinearMap.zero_apply] at h
    rw [LinearMap.zero_apply, ← h, eq_comm]
    have e1 : ∀ ζ' : Idx q, ((tateMap lam (evalHom q M' ζ')).baseChange ℂ) (((inclMap q M' lam ζ).baseChange ℂ) w) =
        ((tateMap lam (evalHom q M' ζ') ∘ₗ inclMap q M' lam ζ).baseChange ℂ) w := fun ζ' => by
      rw [LinearMap.baseChange_comp]; rfl
    refine (Finset.sum_eq_single ζ (fun ζ' _ hne => ?_) (fun h' => (h' (Finset.mem_univ ζ)).elim)).trans ?_
    · rw [compDual_apply, e1, evalMap_comp_inclMap_ne q M' lam hne, LinearMap.baseChange_zero, LinearMap.zero_apply,
        map_zero]
    · rw [compDual_apply, e1, evalMap_comp_inclMap_same, LinearMap.baseChange_id, LinearMap.id_apply]

  have hG : ∀ e : (ZMod q)ˣ, compF q hΦg f hf hfrange (unitLift q e⁻¹) v = 0 := by
    intro e
    have h1 := hζ (ζ₀.pow e)
    rw [← map_zero Ψ] at h1
    have h2 := hΨ h1
    rw [show (idxEquiv ζ₀).symm (ζ₀.pow e) = e from (idxEquiv ζ₀).symm_apply_apply e, Gcomp_apply,
      ← map_zero (CuspForm.diamondLinH 2 (nLift q M' e))] at h2
    have h3 := diamondLinH_injective (nLift q M' e) h2
    exact (LinearEquiv.map_eq_zero_iff _).1 h3
  refine eq_zero_of_forall_compF_eq_zero q hΦg f hf hfrange hfinj v fun u => ?_
  have hu := hG (Units.map PadicInt.toZMod.toMonoidHom u)⁻¹
  rw [inv_inv] at hu
  rw [← hu]
  exact compF_eq_of_toZMod_eq q hΦg f hf hfrange (by rw [toZMod_unitLift]; simp) v

include hf hfrange in
set_option maxHeartbeats 4000000 in

theorem heckeTLinH_diamondLinH_Gcomp (hg : g.IsNewform) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓqM : ¬ ℓ ∣ q * M')
    (hq : ℓ.Coprime q) (hqM : ℓ.Coprime (q ^ 2 * M')) (hℓN : ¬ ℓ ∣ q ^ 2 * M') (e : (ZMod q)ˣ) (v : VK q V) :
    CuspForm.heckeTLinH 2 hℓ hℓN
        (CuspForm.diamondLinH 2 (ZMod.unitOfCoprime ℓ hqM)⁻¹
          (Gcomp q M' hqM' hΦg f hf hfrange (e * ZMod.unitOfCoprime ℓ hq) v)) =
      (ModularFormClass.qCoeff g ℓ : ℂ) • Gcomp q M' hqM' hΦg f hf hfrange e v := by
  have hqℓ : ¬ q ∣ ℓ := fun h => hℓqM ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hℓ).1 h ▸ dvd_mul_right ℓ M')
  obtain ⟨ℓq', hℓq'⟩ := exists_unit_coe_eq_natCast_of_not_dvd q hqℓ
  have hℓq'red : Units.map PadicInt.toZMod.toMonoidHom ℓq' = ZMod.unitOfCoprime ℓ hq := by
    refine Units.ext ?_
    show PadicInt.toZMod (ℓq' : ℤ_[q]) = ((ZMod.unitOfCoprime ℓ hq : (ZMod q)ˣ) : ZMod q)
    rw [hℓq', toZMod_natCast, ZMod.coe_unitOfCoprime]

  rw [Gcomp_apply, Gcomp_apply, diamondLinH_diamondLinH,
    diamondLinH_eq_of_mul_inv_mem _ (nLift q M' e) (by
      rw [mul_inv_mem_levelH_iff, map_mul, map_inv, unitsMap_nLift, unitsMap_nLift,
        unitsMap_unitOfCoprime _ ℓ hqM hq, mul_inv_cancel_right])]

  rw [(CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm (q ^ 2 * M') (levelH q M') 2).2.2.1 ℓ hℓ hℓN, ← map_smul]
  congr 1

  have hidx : compF q hΦg f hf hfrange (unitLift q (e * ZMod.unitOfCoprime ℓ hq)⁻¹) v =
      compF q hΦg f hf hfrange (unitLift q e⁻¹ * ℓq'⁻¹) v := by
    refine compF_eq_of_toZMod_eq q hΦg f hf hfrange ?_ v
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q))
      (show Units.map PadicInt.toZMod.toMonoidHom (unitLift q (e * ZMod.unitOfCoprime ℓ hq)⁻¹) =
          Units.map PadicInt.toZMod.toMonoidHom (unitLift q e⁻¹ * ℓq'⁻¹) by
        rw [map_toZMod_unitLift, map_mul, map_inv, map_toZMod_unitLift, hℓq'red, mul_inv_rev, mul_comm])
    simpa [Units.coe_map] using this
  rw [hidx]
  exact CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform q hg hΦg (f (v : V))
    (mem_span_apply q hΦg f hf hfrange v) (mem_fixed_apply q hΦg f hf hfrange v) hℓ hℓN ℓq' hℓq'
    (unitLift q e⁻¹) _ _ (isComponent_compF q hΦg f hf hfrange _ v) (isComponent_compF q hΦg f hf hfrange _ v)
    _ _ (coe_Ldelta q M' hqM' _) (coe_Ldelta q M' hqM' _)

include hf hfrange in
set_option maxHeartbeats 8000000 in

theorem hecke_clause (hHC : HeckeGenCommute q M') (hg : g.IsNewform)
    (hΨT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (F : SH q M'),
      ((TateModule.rep lam (jacComp q M') (AddMonoid.End (jacComp q M'))
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (levelH q M') ℓ : AddMonoid.End (jacComp q M')))).baseChange ℂ).dualMap (Ψ F) =
        Ψ (CuspForm.heckeTLinH 2 hℓ hℓM F))
    (hΨD : ∀ (d : (ZMod (q ^ 2 * M'))ˣ) (F : SH q M'),
      ((TateModule.rep lam (jacComp q M') (AddMonoid.End (jacComp q M'))
          (ModularCurve.diamondHBar (q ^ 2 * M') (levelH q M') d :
            AddMonoid.End (jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
        Ψ (CuspForm.diamondLinH 2 d F))
    (ℓ : Nat.Primes) (v : VK q V) :
    ((tateHecke q M' lam (ModularCurve.heckeGen ℓ)).baseChange ℂ).dualMap (psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ v) =
      (if (ℓ : ℕ) ∣ q * M' then (0 : ℂ) else ModularFormClass.qCoeff g ℓ) •
        psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ v := by
  by_cases hℓqM : (ℓ : ℕ) ∣ q * M'
  · rw [if_pos hℓqM, zero_smul, tateHecke_heckeGen_of_dvd q M' lam ℓ hℓqM, LinearMap.baseChange_zero]
    exact LinearMap.ext fun w => by rw [LinearMap.dualMap_apply, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  rw [if_neg hℓqM]
  have hℓ : (ℓ : ℕ).Prime := ℓ.2
  have hq : (ℓ : ℕ).Coprime q := (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => hℓqM (hd.mul_right M')
  have hℓN : ¬ (ℓ : ℕ) ∣ q ^ 2 * M' := by
    intro hd
    rcases (Nat.Prime.dvd_mul hℓ).1 hd with h | h
    · exact hℓqM ((Nat.Prime.dvd_of_dvd_pow hℓ h).mul_right M')
    · exact hℓqM (h.mul_left q)
  have hqM : (ℓ : ℕ).Coprime (q ^ 2 * M') := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓN
  rw [dualMap_baseChange_psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ (tateHecke q M' lam (ModularCurve.heckeGen ℓ))
    (fun _ => tateMap lam (ModularCurve.diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹) ∘ₗ
        tateMap lam (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
          ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ))
    (powEquiv q (ZMod.unitOfCoprime ℓ hq)).symm
    (evalMap_comp_tateHecke q M' lam hHC ℓ hℓqM hq hqM), sum_compDual_equiv, psi_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [Equiv.symm_symm, powEquiv_apply, idxEquiv_symm_pow, ← map_smul, ← map_smul]
  congr 1
  rw [LinearMap.baseChange_comp, ← LinearMap.dualMap_comp_dualMap, LinearMap.comp_apply, tateMap_eq_rep, tateMap_eq_rep,
    hΨD, hΨT _ hℓ hℓN]
  congr 1
  exact heckeTLinH_diamondLinH_Gcomp q M' hqM' hΦg f hf hfrange hg hℓ hℓqM hq hqM hℓN _ v

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end Ws41.E4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped TensorProduct MatrixGroups ModularForm

noncomputable section

namespace Ws41
namespace E4

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

theorem mem_Gamma0_of_mem_Gamma {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma N) : γ ∈ Gamma0 N := by
  rw [Gamma0_mem]; exact (Gamma_mem.1 h).2.2.1

section ClauseI

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
  [Algebra ℤ_[lam] ℂ]
  {g : CuspForm (Gamma0 (q ^ 2 * M')) 2} {Φ : 𝔸GL → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
  {V : Type} [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
  (f : V →ₗ[ℂ] AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
  (hfrange : LinearMap.range f =
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))

include hqM' in

theorem slash_eq_of_flat (W : SH q M') (γE γ' τ₁ τ₂ : SL(2, ℤ)) (hmem : γE⁻¹ * τ₁ * γ' * τ₂⁻¹ ∈ Γfull q M') :
    ⇑W ∣[(2 : ℤ)] (conjElem q γE⁻¹ * conjElem q τ₁) = ⇑W ∣[(2 : ℤ)] (conjElem q τ₂ * (conjElem q γ')⁻¹) := by
  refine slash_eq_slash_of_mul_inv_mem q M' W _ _ ?_
  obtain ⟨g', hg', hcoe⟩ := exists_mem_GammaH_coe_eq_conjElem q M' hqM' _ hmem
  have : conjElem q γE⁻¹ * conjElem q τ₁ * (conjElem q τ₂ * (conjElem q γ')⁻¹)⁻¹ =
      conjElem q (γE⁻¹ * τ₁ * γ' * τ₂⁻¹) := by
    rw [conjElem_mul, conjElem_mul, conjElem_mul, conjElem_inv, conjElem_inv]
    group
  rw [this, ← hcoe]
  exact Subgroup.mem_map_of_mem _ hg'

include hf hfrange in
set_option maxHeartbeats 4000000 in

theorem Gcomp_gl2ReductionRep (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (e : (ZMod q)ˣ) (v : VK q V)
    (γ' : SL(2, ℤ)) (hγ'M : γ' ∈ Gamma M')
    (hγ'red : redQ q γ' =
      diagOneElem q (e * (Matrix.GeneralLinearGroup.det (gl2ReductionHom q k))⁻¹)⁻¹ *
        (diagOneElem q (Matrix.GeneralLinearGroup.det (gl2ReductionHom q k))⁻¹ * gl2ReductionHom q k) *
        (diagOneElem q (e * (Matrix.GeneralLinearGroup.det (gl2ReductionHom q k))⁻¹)⁻¹)⁻¹) :
    Gcomp q M' hqM' hΦg f hf hfrange e (gl2ReductionRep q V (gl2ReductionHom q k) v) =
      Lop q M' hqM' γ' (mem_Gamma0_of_mem_Gamma hγ'M)
        (Gcomp q M' hqM' hΦg f hf hfrange (e * (Matrix.GeneralLinearGroup.det (gl2ReductionHom q k))⁻¹) v) := by
  set x := gl2ReductionHom q k with hx
  set d := (Matrix.GeneralLinearGroup.det x)⁻¹ with hd
  set u : ℤ_[q]ˣ := unitLift q e⁻¹ with hu
  set u' : ℤ_[q]ˣ := u * Matrix.GeneralLinearGroup.det (gl2IntegralLift q k) with hu'
  have hdetx : Matrix.GeneralLinearGroup.det x =
      Units.map PadicInt.toZMod.toMonoidHom (Matrix.GeneralLinearGroup.det (gl2IntegralLift q k)) :=
    Ws41.E4Kit.det_gl2ReductionHom q k
  have hū : Units.map PadicInt.toZMod.toMonoidHom u = e⁻¹ := map_toZMod_unitLift q e⁻¹
  have hū' : Units.map PadicInt.toZMod.toMonoidHom u' = e⁻¹ * Matrix.GeneralLinearGroup.det x := by
    rw [hu', map_mul, hū, hdetx]

  set mE : CuspidalType.GL2 q := CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) * x *
    (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u'))⁻¹ with hmE
  have hdetE : Matrix.GeneralLinearGroup.det mE = 1 := by
    rw [hmE, map_mul, map_mul, map_inv, Ws41.E4Kit.det_diagElem, Ws41.E4Kit.det_diagElem, hū', hū]
    group
  obtain ⟨γE, hγEM, hγEred⟩ := Ws41.E4Kit.exists_mem_Gamma_redQ_eq q M' hqM' mE hdetE
  have hcoe1 := coe_compF_gl2ReductionRep q hΦg f hf hfrange k u γE hγEM
    (Ws41.E4Kit.forall_entry_of_redQ_eq q γE mE hγEred) v

  obtain ⟨τ₁, hτ₁c, hτ₁0, hτ₁red⟩ := Ws41.E4Kit.exists_conjElem_eq_of_mem_Gamma0 q M'
    (CuspForm.gammaLift (q ^ 2 * M') (nLift q M' e) : SL(2, ℤ)) (CuspForm.gammaLift (q ^ 2 * M') (nLift q M' e)).2
  obtain ⟨τ₂, hτ₂c, hτ₂0, hτ₂red⟩ := Ws41.E4Kit.exists_conjElem_eq_of_mem_Gamma0 q M'
    (CuspForm.gammaLift (q ^ 2 * M') (nLift q M' (e * d)) : SL(2, ℤ))
    (CuspForm.gammaLift (q ^ 2 * M') (nLift q M' (e * d))).2
  have hg1 : ZMod.unitsMap (dvd_sq_mul q M')
      (CohCarrier.gamma0Units (q ^ 2 * M') ⟨(CuspForm.gammaLift (q ^ 2 * M') (nLift q M' e) : SL(2, ℤ)),
        (CuspForm.gammaLift (q ^ 2 * M') (nLift q M' e)).2⟩) = e := by
    rw [Subtype.coe_eta, CuspForm.gamma0Units_gammaLift, unitsMap_nLift]
  have hg2 : ZMod.unitsMap (dvd_sq_mul q M')
      (CohCarrier.gamma0Units (q ^ 2 * M') ⟨(CuspForm.gammaLift (q ^ 2 * M') (nLift q M' (e * d)) : SL(2, ℤ)),
        (CuspForm.gammaLift (q ^ 2 * M') (nLift q M' (e * d))).2⟩) = e * d := by
    rw [Subtype.coe_eta, CuspForm.gamma0Units_gammaLift, unitsMap_nLift]
  rw [hg1] at hτ₁red
  rw [hg2] at hτ₂red

  have hW : compF q hΦg f hf hfrange u' v = compF q hΦg f hf hfrange (unitLift q (e * d)⁻¹) v := by
    refine compF_eq_of_toZMod_eq q hΦg f hf hfrange ?_ v
    have := congrArg (fun w : (ZMod q)ˣ => (w : ZMod q))
      (show Units.map PadicInt.toZMod.toMonoidHom u' = Units.map PadicInt.toZMod.toMonoidHom (unitLift q (e * d)⁻¹) by
        rw [hū', map_toZMod_unitLift, hd, mul_inv_rev, inv_inv, mul_comm])
    simpa [Units.coe_map] using this

  have hmem : γE⁻¹ * τ₁ * γ' * τ₂⁻¹ ∈ Γfull q M' := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← Ws41.E4Kit.redQ_eq_one_iff_mem_Gamma, map_mul, map_mul, map_mul, map_inv, map_inv, hγEred, hτ₁red,
        hγ'red, hτ₂red, hmE, hū, hū', hd]
      exact Ws41.E4Kit.key_identity q x e
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (mem_Gamma0_of_mem_Gamma hγEM)) hτ₁0) (mem_Gamma0_of_mem_Gamma hγ'M))
        (Subgroup.inv_mem _ hτ₂0)

  apply DFunLike.coe_injective
  rw [Gcomp_apply, CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD _ _ 2), coe_Ldelta, hcoe1,
    slash_SL_slash_heckeDiagMatrix, ← coe_Ldelta q M' hqM', hW, ← SlashAction.slash_mul, coe_Lop, Gcomp_apply,
    CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD _ _ 2), ← SlashAction.slash_mul, ← coe_SL_eq_mapGL,
    ← coe_SL_eq_mapGL, ← hτ₁c, ← hτ₂c]
  exact slash_eq_of_flat q M' hqM' _ γE γ' τ₁ τ₂ hmem

include hf hfrange in
set_option maxHeartbeats 8000000 in

theorem gl2_clause (hGL : GL2Laws q M') (ζ₀ : Idx q) (Ψ : SH q M' →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TJ q M' lam))
    (hlev : ∀ (e : (ZMod q)ˣ) (γ : SL(2, ℤ)), γ ∈ Gamma M' →
      ∃ γ' : SL(2, ℤ), ∃ hγ' : γ' ∈ Gamma M',
        redQ q γ' = diagOneElem q e⁻¹ * redQ q γ * (diagOneElem q e⁻¹)⁻¹ ∧
        ∀ F : SH q M', ((tateMap lam (levelOp q M' (ζ₀.pow e) γ)).baseChange ℂ).dualMap (Ψ F) =
          Ψ (Lop q M' hqM' γ' (mem_Gamma0_of_mem_Gamma hγ') F))
    (x : CuspidalType.GL2 q) (v : VK q V) :
    psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ (gl2ReductionRep q V x v) =
      ((tateGL2 q M' lam x⁻¹).baseChange ℂ).dualMap (psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ v) := by
  obtain ⟨k, rfl⟩ := gl2ReductionHom_surjective q x
  set x := gl2ReductionHom q k with hx
  set d := (Matrix.GeneralLinearGroup.det x)⁻¹ with hd
  have hdet1 : Matrix.GeneralLinearGroup.det (x⁻¹ * (diagOneElem q d)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_inv, Ws41.E4Kit.det_diagOneElem, hd, inv_inv, inv_mul_cancel]
  obtain ⟨γ₁, hγ₁M, hγ₁red⟩ := Ws41.E4Kit.exists_mem_Gamma_redQ_eq q M' hqM' _ hdet1
  have hxinv : x⁻¹ = redQ q γ₁ * diagOneElem q d := by rw [hγ₁red, inv_mul_cancel_right]
  rw [hxinv, dualMap_baseChange_psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ
      (tateGL2 q M' lam (redQ q γ₁ * diagOneElem q d)) (fun ζ => tateMap lam (levelOp q M' ζ γ₁⁻¹))
      (powEquiv q d).symm
      (evalMap_comp_tateGL2_redQ_mul_diagOneElem q M' lam hGL γ₁ (mem_Gamma0_of_mem_Gamma hγ₁M) d),
    sum_compDual_equiv, psi_apply]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [Equiv.symm_symm, powEquiv_apply, idxEquiv_symm_pow]
  congr 1
  set e := (idxEquiv ζ₀).symm ζ with he
  have hζ : ζ.pow d = ζ₀.pow (e * d) := by rw [← pow_idxEquiv_symm ζ₀ ζ, Idx.pow_pow]
  obtain ⟨γ', hγ'M, hγ'red, hγ'L⟩ := hlev (e * d) γ₁⁻¹ (inv_mem hγ₁M)
  rw [hζ, hγ'L]
  congr 1
  have h1 : (redQ q γ₁)⁻¹ = diagOneElem q d * x := by rw [hγ₁red, mul_inv_rev, inv_inv, inv_inv]
  refine Gcomp_gl2ReductionRep q M' hqM' hΦg f hf hfrange k e v γ' hγ'M ?_
  rw [hγ'red, map_inv, h1]

end ClauseI
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end Ws41.E4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped TensorProduct MatrixGroups ModularForm

noncomputable section

namespace Ws41
namespace E4

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

section LevelConj

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

theorem levelOp_pow_inv_eq_of_gl2Laws (hGL : GL2Laws q M') (ζ : Idx q) (d : (ZMod q)ˣ)
    (γ γ' : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (hγ' : γ' ∈ CongruenceSubgroup.Gamma0 M')
    (hred : redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹) :
    levelOp q M' (ζ.pow d⁻¹) γ = levelOp q M' ζ γ' := by
  have hγi : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ
  have hγ'i : γ'⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ'
  have hredi : redQ q γ'⁻¹ = diagOneElem q d * redQ q γ⁻¹ * (diagOneElem q d)⁻¹ := by
    rw [map_inv, hred, map_inv, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  have key : gl2Jac q M' (redQ q γ'⁻¹) =
      gl2Jac q M' (diagOneElem q d) * gl2Jac q M' (redQ q γ⁻¹) * gl2Jac q M' (diagOneElem q d⁻¹) := by
    rw [hredi, map_mul, map_mul, Ws41.E4Kit.diagOneElem_inv]
  have key' : ∀ x : Jac q M',
      slJac q M' γ'⁻¹ x = diagJac q M' d (slJac q M' γ⁻¹ (diagJac q M' d⁻¹ x)) := fun x => by
    have hx := congrArg (fun T : AddMonoid.End (Jac q M') => T x) key
    simp only [AddMonoid.End.coe_mul, Function.comp_apply, gl2Jac_redQ hGL _ hγ'i,
      gl2Jac_redQ hGL _ hγi, gl2Jac_diagOneElem hGL] at hx
    exact hx
  refine AddMonoidHom.ext fun y => ?_
  have h := congrArg (fun z : Jac q M' => z.eval ζ) (key' (Jac.mk fun _ => y))
  simp only [slJac_eval, diagJac_eval, Jac.eval_mk, inv_inv] at h
  exact h.symm

end LevelConj
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

section Final

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
  [Algebra ℤ_[lam] ℂ]

set_option maxHeartbeats 8000000 in

theorem level_clause (hGL : GL2Laws q M') (ζ₀ : Idx q)
    (Ψ : SH q M' →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TJ q M' lam))
    (hΨL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (F : SH q M'),
      ((TateModule.rep lam (jacComp q M') (AddMonoid.End (jacComp q M'))
          (levelOp q M' ζ₀ γ : AddMonoid.End (jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
        Ψ (Lop q M' hqM' γ hγ F)) :
    ∀ (e : (ZMod q)ˣ) (γ : SL(2, ℤ)), γ ∈ Gamma M' →
      ∃ γ' : SL(2, ℤ), ∃ hγ' : γ' ∈ Gamma M',
        redQ q γ' = diagOneElem q e⁻¹ * redQ q γ * (diagOneElem q e⁻¹)⁻¹ ∧
        ∀ F : SH q M', ((tateMap lam (levelOp q M' (ζ₀.pow e) γ)).baseChange ℂ).dualMap (Ψ F) =
          Ψ (Lop q M' hqM' γ' (mem_Gamma0_of_mem_Gamma hγ') F) := by
  intro e γ hγ
  have hdet : Matrix.GeneralLinearGroup.det (diagOneElem q e⁻¹ * redQ q γ * (diagOneElem q e⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, Ws41.E4Kit.det_redQ, mul_one, mul_inv_cancel]
  obtain ⟨γ', hγ'M, hγ'red⟩ := Ws41.E4Kit.exists_mem_Gamma_redQ_eq q M' hqM' _ hdet
  refine ⟨γ', hγ'M, hγ'red, fun F => ?_⟩
  have hop : levelOp q M' (ζ₀.pow e) γ = levelOp q M' ζ₀ γ' := by
    have := levelOp_pow_inv_eq_of_gl2Laws hGL ζ₀ e⁻¹ γ γ' (mem_Gamma0_of_mem_Gamma hγ)
      (mem_Gamma0_of_mem_Gamma hγ'M) hγ'red
    rwa [inv_inv] at this
  rw [hop, tateMap_eq_rep, hΨL γ' (mem_Gamma0_of_mem_Gamma hγ'M) F]

end Final
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end Ws41.E4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4.Arch P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41 P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span.Ws41.E4"

set_option maxHeartbeats 8000000 in
open Ws41.E4 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
    [Algebra ℤ_[lam] ℂ]
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hHC : ModularCurve.FullLevel.HeckeGenCommute q M')
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNewform)
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ)) :
    ∃ ψ : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
        Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')),
      Function.Injective ψ ∧
      (∀ (x : CuspidalType.GL2 q)
          (v : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
          ψ (LocalNewvector.gl2ReductionRep q V x v) =
            ((ModularCurve.FullLevel.tateGL2 q M' lam x⁻¹).baseChange ℂ).dualMap (ψ v)) ∧
      (∀ (ℓ : Nat.Primes)
          (v : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
          ((ModularCurve.FullLevel.tateHecke q M' lam (ModularCurve.heckeGen ℓ)).baseChange ℂ).dualMap (ψ v) =
            (if (ℓ : ℕ) ∣ q * M' then (0 : ℂ) else ModularFormClass.qCoeff g ℓ) • ψ v) := by
  obtain ⟨ζ₀, Ψ, hΨinj, hΨT, hΨD, hΨL⟩ :=
    ModularCurve.FullLevel.exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm q M' lam hin hLA
      (Lop q M' hqM') (coe_Lop q M' hqM') (dualMap_Lop_mem q M' hqM')
  refine ⟨psi q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ,
    psi_injective q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ hΨinj hfinj, fun x v => ?_, fun ℓ v => ?_⟩
  · exact gl2_clause q M' hqM' lam hΦg f hf hfrange hGL ζ₀ Ψ (level_clause q M' hqM' lam hGL ζ₀ Ψ hΨL) x v
  · exact hecke_clause q M' hqM' lam hΦg f hf hfrange ζ₀ Ψ hHC hg hΨT hΨD ℓ v

end S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span (solution)
