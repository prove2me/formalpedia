-- Prove2me | solution 1 for ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/255e1b7b-2f2a-556f-b845-2b0eed2fe936

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Inst
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH
import Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH
import Theorems.Thm_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
import Theorems.Thm_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Theorems.Thm_CohCarrier_diamondRaw_comm
import Theorems.Thm_CohCarrier_exists_gamma0_lift_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE Ihara.instGroupIharaAmalgam CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0"
p2m_attr_erase "simp" "CuspForm.PeterssonCoset.mapGL_apply CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Module

namespace RTJH

section Transport

variable {R : Type*} [CommRing R] {Wm : Type*} [AddCommGroup Wm] [Module R Wm] {n : ℕ}
variable (bR : Basis (Fin n) R Wm)

abbrev Φm : Module.End R Wm ≃ₐ[R] Matrix (Fin n) (Fin n) R := LinearMap.toMatrixAlgEquiv bR

theorem Φm_apply (x : Module.End R Wm) : Φm bR x = LinearMap.toMatrix bR bR x := rfl

abbrev ΦmH : Module.End R Wm →ₐ[R] Matrix (Fin n) (Fin n) R :=
  (Φm bR : Module.End R Wm →ₐ[R] Matrix (Fin n) (Fin n) R)

@[scoped simp] theorem ΦmH_apply (x : Module.End R Wm) : ΦmH bR x = Φm bR x := rfl

theorem toLin'_Φm_apply (x : Module.End R Wm) (w : Wm) :
    Matrix.toLin' (Φm bR x) (bR.equivFun w) = bR.equivFun (x w) := by
  rw [Matrix.toLin'_apply, Φm_apply, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

theorem toLin'_Φm_comp (x : Module.End R Wm) :
    Matrix.toLin' (Φm bR x) ∘ₗ (bR.equivFun : Wm →ₗ[R] (Fin n → R)) =
      (bR.equivFun : Wm →ₗ[R] (Fin n → R)) ∘ₗ x := by
  ext w
  exact congrFun (toLin'_Φm_apply bR x w) _

variable (A : Subalgebra R (Module.End R Wm))

abbrev idxEquiv : ↥A ≃ₐ[R] ↥(A.map (ΦmH bR)) :=
  (Φm bR).subalgebraMap A

theorem coe_idxEquiv (a : A) :
    ((idxEquiv bR A a : ↥(A.map (ΦmH bR))) :
      Matrix (Fin n) (Fin n) R) = Φm bR a :=
  AlgEquiv.subalgebraMap_apply_coe _ _ _

theorem finrank_iInf_eigenspace_Φm
    (g : ↥(A.map (ΦmH bR)) → R) :
    Module.finrank R ↥(⨅ a' : ↥(A.map (ΦmH bR)),
        Module.End.eigenspace (Matrix.toLin' (a' : Matrix (Fin n) (Fin n) R)) (g a')) =
      Module.finrank R ↥(⨅ a : A, Module.End.eigenspace (a : Module.End R Wm)
        (g (idxEquiv bR A a))) := by
  set E' := ⨅ a' : ↥(A.map (ΦmH bR)),
        Module.End.eigenspace (Matrix.toLin' (a' : Matrix (Fin n) (Fin n) R)) (g a') with hE'
  have hcomap : E'.comap (bR.equivFun : Wm →ₗ[R] (Fin n → R)) =
      ⨅ a : A, Module.End.eigenspace (a : Module.End R Wm) (g (idxEquiv bR A a)) := by
    rw [hE', Submodule.comap_iInf]
    rw [← Equiv.iInf_comp (idxEquiv bR A).toEquiv]
    refine iInf_congr fun a => ?_
    ext w
    simp only [Submodule.mem_comap, Module.End.mem_eigenspace_iff, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, coe_idxEquiv]
    change Matrix.toLin' (Φm bR a) (bR.equivFun w) = _ ↔ _
    rw [toLin'_Φm_apply, ← map_smul]
    exact bR.equivFun.injective.eq_iff
  rw [← hcomap, Submodule.comap_equiv_eq_map_symm]
  exact (LinearEquiv.finrank_map_eq _ _).symm

theorem exists_bijective_of_basis {d : ℕ} (β : Module.Basis (Fin d) A Wm) :
    ∃ v : Fin d → (Fin n → R), Function.Bijective
      (fun c : Fin d → ↥(A.map (ΦmH bR)) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) R).mulVec (v k))) := by
  refine ⟨fun k => bR.equivFun (β k), ?_⟩
  let e0 : (Fin d → ↥(A.map (ΦmH bR))) ≃ (Fin d → A) :=
    Equiv.arrowCongr (Equiv.refl _) (idxEquiv bR A).symm.toEquiv
  have hfac : (fun c : Fin d → ↥(A.map (ΦmH bR)) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) R).mulVec (bR.equivFun (β k)))) =
      (bR.equivFun : Wm → (Fin n → R)) ∘ (β.equivFun.symm : (Fin d → A) → Wm) ∘ e0 := by
    funext c
    simp only [Function.comp_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ((c k : Matrix (Fin n) (Fin n) R)) = Φm bR ((idxEquiv bR A).symm (c k) : A) := by
      have := coe_idxEquiv bR A ((idxEquiv bR A).symm (c k))
      rw [AlgEquiv.apply_symm_apply] at this
      exact this
    rw [hk, ← Matrix.toLin'_apply, toLin'_Φm_apply]
    rfl
  rw [hfac]
  exact bR.equivFun.bijective.comp (β.equivFun.symm.bijective.comp e0.bijective)

end Transport

section Stable

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CohCarrier ModularCurve.Period
open scoped MatrixGroups

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem heckeT_apply_eq_sum (φ : H1 M Hs A) (u : ↥(GammaH M Hs))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)))] :
    heckeT M Hs ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)),
        φ (Additive.ofMul (conjL M Hs ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem trace_conjUpperMat (X : SL(2, ℤ)) (hX : (ℓ : ℤ) ∣ X 0 1) :
    ((conjUpperMat ℓ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjUpperMat]

theorem trace_sq_conj_pow (γ r : SL(2, ℤ)) (m : ℕ)
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((r⁻¹ * γ ^ m * r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  obtain ⟨ε, δ, h, hε, rfl⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four γ hγ
  have hu : ∀ n : ℕ, ((r⁻¹ * (δ * ModularGroup.T ^ h * δ⁻¹) ^ n * r : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    intro n
    rw [conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      show r⁻¹ * (δ * ModularGroup.T ^ (h * (n : ℤ)) * δ⁻¹) * r =
        (r⁻¹ * δ) * (ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹) by group,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      show ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹ * (r⁻¹ * δ) = ModularGroup.T ^ (h * (n : ℤ)) by group,
      ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
    ring
  rcases hε with rfl | rfl
  · rw [one_mul, hu]; norm_num
  · rw [neg_one_mul, neg_pow]
    rcases neg_one_pow_eq_or SL(2, ℤ) m with h1 | h1
    · rw [h1, one_mul, hu]; norm_num
    · rw [h1, neg_one_mul, mul_neg, neg_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
        neg_sq, hu]
      norm_num

theorem heckeT_isParabolicHom (φ : H1 M Hs A)
    (hφ : IsParabolicHom (GammaH M Hs) φ) :
    IsParabolicHom (GammaH M Hs) (heckeT M Hs ℓ A φ) := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ))) := Fintype.ofFinite _
  rw [heckeT_apply_eq_sum]
  refine Finset.sum_eq_zero fun O _ => hφ _ ?_
  set x : ↥(GammaHUpper M Hs ℓ) := ⟨O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem _ γ O.out⟩ with hxdef
  have hx : ((conjL M Hs ℓ x : ↥(GammaH M Hs)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH M Hs)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M Hs ℓ x) := rfl
  rw [hx, trace_conjUpperMat, hxdef]
  show ((((O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out : ↥(GammaH M Hs)) :
    SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact trace_sq_conj_pow _ _ _ hγ

theorem diamondRaw_isParabolicHom (σ : Gamma0 M) (φ : H1 M Hs A)
    (hφ : IsParabolicHom (GammaH M Hs) φ) :
    IsParabolicHom (GammaH M Hs) (diamondRaw M Hs A σ φ) := by
  intro γ hγ
  show φ (Additive.ofMul (conjHom M Hs σ γ)) = 0
  refine hφ _ ?_
  show ((((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    show (σ : SL(2, ℤ))⁻¹ * ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ))) = γ by group]
  exact hγ

theorem diamondL_isParabolicHom [NeZero M] (R : Type) [CommRing R] (d : (ZMod M)ˣ) (φ : H1 M Hs R)
    (hφ : IsParabolicHom (GammaH M Hs) φ) :
    IsParabolicHom (GammaH M Hs) (diamondL M Hs R d φ) :=
  diamondRaw_isParabolicHom M Hs _ φ hφ

theorem coresAdd_comp {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex]
    {B : Type*} [AddCommGroup B] (f : A →+ B) (ψ : Additive ↥K →+ A) :
    coresAdd K (f.comp ψ) = f.comp (coresAdd K ψ) := by
  ext g
  simp only [coresAdd, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

theorem heckeT_eq_coresAdd (φ : H1 M Hs A) :
    heckeT M Hs ℓ A φ = coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M Hs ℓ))) := rfl

theorem heckeT_comp_coeff {B : Type*} [AddCommGroup B] (f : A →+ B) (φ : H1 M Hs A) :
    heckeT M Hs ℓ B (f.comp φ) = f.comp (heckeT M Hs ℓ A φ) := by
  rw [heckeT_eq_coresAdd, heckeT_eq_coresAdd, ← coresAdd_comp]
  rfl

theorem diamondL_comp_coeff [NeZero M] (R R' : Type) [CommRing R] [CommRing R'] (d : (ZMod M)ˣ)
    (f : R →+ R') (φ : H1 M Hs R) :
    diamondL M Hs R' d (f.comp φ) = f.comp (diamondL M Hs R d φ) := rfl

end Stable

section Parabolic

open CongruenceSubgroup CohCarrier ModularCurve.Period
open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ)

theorem isCongruenceSubgroup_GammaH : IsCongruenceSubgroup (GammaH M Hs) := by
  refine ⟨M, NeZero.ne _, fun A hA => ?_⟩
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact h10
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    apply Units.ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]; exact one_mem Hs

scoped instance finiteIndex_GammaH : (GammaH M Hs).FiniteIndex := (isCongruenceSubgroup_GammaH M Hs).finiteIndex

abbrev parR (R : Type) [CommRing R] : Submodule R (H1 M Hs R) :=
  parabolicHoms R (GammaH M Hs) R

theorem heckeT_mem_parR (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (φ : H1 M Hs R)
    (hφ : φ ∈ parR M Hs R) : heckeT M Hs ℓ R φ ∈ parR M Hs R :=
  heckeT_isParabolicHom M Hs ℓ φ hφ

theorem diamondL_mem_parR (R : Type) [CommRing R] (d : (ZMod M)ˣ) (φ : H1 M Hs R)
    (hφ : φ ∈ parR M Hs R) : diamondL M Hs R d φ ∈ parR M Hs R :=
  diamondL_isParabolicHom M Hs R d φ hφ

abbrev Idx (S : Set ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ (ℓ ∉ S ∨ ℓ ∣ M)} ⊕ (ZMod M)ˣ

def TparI (S : Set ℕ) (R : Type) [CommRing R] : Idx M S → Module.End R ↥(parR M Hs R)
  | Sum.inl i =>
      haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
      (heckeTL M Hs R i.1).restrict fun φ hφ => heckeT_mem_parR M Hs R i.1 φ hφ
  | Sum.inr d => (diamondL M Hs R d).restrict fun φ hφ => diamondL_mem_parR M Hs R d φ hφ

theorem coe_TparI_inl (S : Set ℕ) (R : Type) [CommRing R] (i : {ℓ : ℕ // ℓ.Prime ∧ (ℓ ∉ S ∨ ℓ ∣ M)})
    (φ : ↥(parR M Hs R)) :
    ((TparI M Hs S R (Sum.inl i) φ : ↥(parR M Hs R)) : H1 M Hs R) =
      (haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩; heckeT M Hs i.1 R φ) := rfl

theorem coe_TparI_inr (S : Set ℕ) (R : Type) [CommRing R] (d : (ZMod M)ˣ) (φ : ↥(parR M Hs R)) :
    ((TparI M Hs S R (Sum.inr d) φ : ↥(parR M Hs R)) : H1 M Hs R) = diamondL M Hs R d φ := rfl

def castPar (R : Type) [CommRing R] : ↥(parR M Hs ℤ) →+ ↥(parR M Hs R) where
  toFun φ := ⟨(Int.castAddHom R).comp (φ : H1 M Hs ℤ), by
    intro γ hγ
    show (Int.castAddHom R) ((φ : H1 M Hs ℤ) (Additive.ofMul γ)) = 0
    rw [φ.2 γ hγ, map_zero]⟩
  map_zero' := by ext; simp
  map_add' φ ψ := by ext; simp

theorem coe_castPar (R : Type) [CommRing R] (φ : ↥(parR M Hs ℤ)) :
    ((castPar M Hs R φ : ↥(parR M Hs R)) : H1 M Hs R) =
      (Int.castAddHom R).comp (φ : H1 M Hs ℤ) := rfl

theorem castPar_TparI (S : Set ℕ) (R : Type) [CommRing R] (i : Idx M S) (φ : ↥(parR M Hs ℤ)) :
    castPar M Hs R (TparI M Hs S ℤ i φ) = TparI M Hs S R i (castPar M Hs R φ) := by
  rcases i with i | d
  · haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
    apply Subtype.ext
    show (Int.castAddHom R).comp (heckeT M Hs i.1 ℤ φ) =
      heckeT M Hs i.1 R ((Int.castAddHom R).comp (φ : H1 M Hs ℤ))
    rw [heckeT_comp_coeff]
  · apply Subtype.ext
    show (Int.castAddHom R).comp (diamondL M Hs ℤ d φ) =
      diamondL M Hs R d ((Int.castAddHom R).comp (φ : H1 M Hs ℤ))
    rw [diamondL_comp_coeff]

variable {M Hs}
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ))

def Mint (S : Set ℕ) (i : Idx M S) : Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix b b (TparI M Hs S ℤ i)

variable {R : Type} [CommRing R] (bR : Module.Basis (Fin n) R ↥(parR M Hs R))
  (hbR : ∀ i, (bR i : H1 M Hs R) = (Int.castAddHom R).comp (b i : H1 M Hs ℤ))

include hbR in
theorem castPar_b (j : Fin n) : castPar M Hs R (b j) = bR j := Subtype.ext (hbR j).symm

include hbR in

theorem toMatrix_TparI (S : Set ℕ) (i : Idx M S) :
    LinearMap.toMatrix bR bR (TparI M Hs S R i) = (Mint b S i).map (Int.cast : ℤ → R) := by
  ext k j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, Mint]
  have hexp : TparI M Hs S ℤ i (b j) = ∑ k, (LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j) • b k := by
    conv_lhs => rw [← b.sum_repr (TparI M Hs S ℤ i (b j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.toMatrix_apply]
  have h1 : TparI M Hs S R i (bR j) =
      ∑ k, ((LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j : ℤ) : R) • bR k := by
    rw [← castPar_b b bR hbR j, ← castPar_TparI, hexp, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, castPar_b b bR hbR k]
    exact (Int.cast_smul_eq_zsmul R _ _).symm
  rw [h1]
  have h2 : bR.repr (∑ k, ((LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j : ℤ) : R) • bR k) =
      Finsupp.equivFunOnFinite.symm fun k => ((LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j : ℤ) : R) := by
    rw [← Module.Basis.equivFun_symm_apply]
    apply bR.repr.symm.injective
    simp [Module.Basis.equivFun]
  rw [h2]
  rfl

include hbR in

theorem map_adjoin_TparI (S : Set ℕ) :
    (Algebra.adjoin R (Set.range (TparI M Hs S R))).map (ΦmH bR) =
      Algebra.adjoin R (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → R)) := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  have h : (ΦmH bR : Module.End R ↥(parR M Hs R) → Matrix (Fin n) (Fin n) R) ∘ TparI M Hs S R =
      fun i => (Mint b S i).map (Int.cast : ℤ → R) := by
    funext i
    show Φm bR (TparI M Hs S R i) = _
    rw [Φm_apply, toMatrix_TparI b bR hbR]
  rw [h]

end Parabolic

section OverC

open CongruenceSubgroup CohCarrier ModularCurve.Period

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (S : Set ℕ)

theorem genSet_eq (R : Type) [CommRing R] :
    {T : Module.End R ↥(parabolicHoms R (GammaH M Hs) R) |
        (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          ((T v : ↥(parabolicHoms R (GammaH M Hs) R)) : H1 M Hs R) =
            heckeT M Hs ℓ R (v : H1 M Hs R)) ∨
        (∃ d : (ZMod M)ˣ, ∀ v,
          ((T v : ↥(parabolicHoms R (GammaH M Hs) R)) : H1 M Hs R) =
            diamondL M Hs R d (v : H1 M Hs R))} =
      Set.range (TparI M Hs S R) := by
  ext T
  constructor
  · rintro (⟨ℓ, hℓ, hℓS, h⟩ | ⟨d, h⟩)
    · refine ⟨Sum.inl ⟨ℓ, hℓ, hℓS⟩, ?_⟩
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact (h v).symm
    · refine ⟨Sum.inr d, ?_⟩
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact (h v).symm
  · rintro ⟨(⟨ℓ, hℓ, hℓS⟩ | d), rfl⟩
    · exact Or.inl ⟨ℓ, hℓ, hℓS, fun v => rfl⟩
    · exact Or.inr ⟨d, fun v => rfl⟩

variable (hSfin : S.Finite)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ))
  (bC : Module.Basis (Fin n) ℂ ↥(parR M Hs ℂ))
  (hbC : ∀ i, (bC i : H1 M Hs ℂ) = (Int.castAddHom ℂ).comp (b i : H1 M Hs ℤ))

include hSfin hbC in
set_option maxHeartbeats 8000000 in

theorem descent_hypotheses :
    (∃ v : Fin 2 → (Fin n → ℂ), Function.Bijective
      (fun c : Fin 2 → ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k)))) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = 2 := by
  obtain ⟨⟨β⟩, hmult⟩ :=
    CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two M Hs S hSfin
  rw [genSet_eq M Hs S ℂ] at β hmult
  have hmap := map_adjoin_TparI b bC hbC S
  rw [← hmap]
  refine ⟨exists_bijective_of_basis bC _ β, fun χ => ?_⟩
  rw [finrank_iInf_eigenspace_Φm bC (Algebra.adjoin ℂ (Set.range (TparI M Hs S ℂ))) χ]
  exact hmult (χ.comp (idxEquiv bC (Algebra.adjoin ℂ (Set.range (TparI M Hs S ℂ)))).toAlgHom)

end OverC

section Comm

open CongruenceSubgroup CohCarrier ModularCurve.Period
open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (R : Type) [CommRing R]

theorem heckeTL_comm_heckeTL (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) [NeZero ℓ] [NeZero ℓ'] :
    heckeTL M Hs R ℓ * heckeTL M Hs R ℓ' = heckeTL M Hs R ℓ' * heckeTL M Hs R ℓ := by
  by_cases h : ℓ = ℓ'
  · subst h; rfl
  · refine LinearMap.ext fun φ => ?_
    exact CohCarrier.heckeT_comm_of_prime M Hs ℓ ℓ' hℓ ((Nat.coprime_primes hℓ hℓ').mpr h) φ

theorem heckeTL_comm_diamondL (ℓ : ℕ) [NeZero ℓ] (u : (ZMod M)ˣ) :
    heckeTL M Hs R ℓ * diamondL M Hs R u = diamondL M Hs R u * heckeTL M Hs R ℓ := by
  obtain ⟨σ, hσ, hdvd⟩ := CohCarrier.exists_gamma0_lift_dvd M ℓ u
  refine LinearMap.ext fun φ => ?_
  show heckeT M Hs ℓ R (diamondL M Hs R u φ) = diamondL M Hs R u (heckeT M Hs ℓ R φ)
  rw [diamondL_eq_diamondRaw M Hs R u σ hσ, diamondL_eq_diamondRaw M Hs R u σ hσ]
  exact CohCarrier.heckeT_diamondRaw_comm M Hs ℓ σ hdvd φ

theorem diamondL_comm_diamondL (u v : (ZMod M)ˣ) :
    diamondL M Hs R u * diamondL M Hs R v = diamondL M Hs R v * diamondL M Hs R u := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective M u
  obtain ⟨τ, hτ⟩ := gamma0Units_surjective M v
  refine LinearMap.ext fun φ => ?_
  show diamondL M Hs R u (diamondL M Hs R v φ) = diamondL M Hs R v (diamondL M Hs R u φ)
  rw [diamondL_eq_diamondRaw M Hs R u σ hσ, diamondL_eq_diamondRaw M Hs R v τ hτ,
    diamondL_eq_diamondRaw M Hs R u σ hσ, diamondL_eq_diamondRaw M Hs R v τ hτ]
  exact CohCarrier.diamondRaw_comm M Hs σ τ φ

theorem TparI_comm (S : Set ℕ) (i j : Idx M S) :
    TparI M Hs S R i * TparI M Hs S R j = TparI M Hs S R j * TparI M Hs S R i := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rcases i with i | u <;> rcases j with j | v
  · haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
    haveI : NeZero j.1 := ⟨j.2.1.ne_zero⟩
    exact congrArg (fun T : Module.End R (H1 M Hs R) => T (φ : H1 M Hs R))
      (heckeTL_comm_heckeTL M Hs R i.1 j.1 i.2.1 j.2.1)
  · haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
    exact congrArg (fun T : Module.End R (H1 M Hs R) => T (φ : H1 M Hs R))
      (heckeTL_comm_diamondL M Hs R i.1 v)
  · haveI : NeZero j.1 := ⟨j.2.1.ne_zero⟩
    exact congrArg (fun T : Module.End R (H1 M Hs R) => T (φ : H1 M Hs R))
      (heckeTL_comm_diamondL M Hs R j.1 u).symm
  · exact congrArg (fun T : Module.End R (H1 M Hs R) => T (φ : H1 M Hs R))
      (diamondL_comm_diamondL M Hs R u v)

variable {M Hs}

theorem Mint_comm {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ)) (S : Set ℕ) (i j : Idx M S) :
    Mint b S i * Mint b S j = Mint b S j * Mint b S i := by
  rw [Mint, Mint, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, TparI_comm]

end Comm

section RowFree

open CongruenceSubgroup CohCarrier ModularCurve.Period

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ))
  (bC : Module.Basis (Fin n) ℂ ↥(parR M Hs ℂ))
  (hbC : ∀ i, (bC i : H1 M Hs ℂ) = (Int.castAddHom ℂ).comp (b i : H1 M Hs ℤ))

include hSfin hbC in

theorem rowfree (K : Type) [Field K] [CharZero K] :
    ∃ w : Fin 2 → (Fin n → K), Function.Bijective
      (fun c : Fin 2 → ↥(Algebra.adjoin K (Set.range fun i : Idx M S =>
          ((Mint b S i).transpose).map (Int.cast : ℤ → K))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) K).mulVec (w k))) := by
  obtain ⟨hfree, hmult⟩ := descent_hypotheses M Hs S hSfin b bC hbC
  exact Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast n 2 (Mint b S)
    (Mint_comm b S) hfree hmult K

end RowFree

section Tate

open CongruenceSubgroup CohCarrier ModularCurve ModularCurve.Period
open scoped TensorProduct

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

def idx : Gen M S → Idx M S
  | .T ℓ hℓ hℓS _ => Sum.inl ⟨ℓ, hℓ, Or.inl hℓS⟩
  | .U q hq hqM => Sum.inl ⟨q, hq, Or.inr hqM⟩
  | .dia d => Sum.inr d

theorem idx_surjective : Function.Surjective (idx M S) := by
  classical
  rintro (⟨ℓ, hℓ, h⟩ | d)
  · by_cases hM : ℓ ∣ M
    · exact ⟨.U ℓ hℓ hM, rfl⟩
    · have hS : ℓ ∉ S := by
        rcases h with h | h
        · exact h
        · exact absurd h hM
      exact ⟨.T ℓ hℓ hS hM, rfl⟩
  · exact ⟨.dia d, rfl⟩

theorem opFamily_apply_eq (R : Type) [CommRing R] (g : Gen M S) (φ : ↥(parR M Hs R)) :
    opFamily M Hs S R g (φ : H1 M Hs R) = ((TparI M Hs S R (idx M S g) φ : ↥(parR M Hs R)) : H1 M Hs R) := by
  rcases g with ⟨ℓ, hℓ, hℓS, hℓM⟩ | ⟨q, hq, hqM⟩ | d <;> rfl

variable (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
variable (G : Gen M S → Module.End ℤ_[p] T)
variable (Φ : H1 M Hs ℤ_[p] →ₗ[ℤ_[p]] (T →ₗ[ℤ_[p]] ℤ_[p]))
variable (hΦeq : ∀ (g : Gen M S) (v : H1 M Hs ℤ_[p]), v ∈ parR M Hs ℤ_[p] →
    Φ (opFamily M Hs S ℤ_[p] g v) = (Φ v) ∘ₗ G g)
variable (hΦsurj : (parR M Hs ℤ_[p]).map Φ = ⊤)
variable (hΦinj : ∀ v ∈ parR M Hs ℤ_[p], Φ v = 0 → v = 0)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ))
  (bp : Module.Basis (Fin n) ℤ_[p] ↥(parR M Hs ℤ_[p]))
  (hbp : ∀ i, (bp i : H1 M Hs ℤ_[p]) = (Int.castAddHom ℤ_[p]).comp (b i : H1 M Hs ℤ))

def eΦ (hΦsurj : (parR M Hs ℤ_[p]).map Φ = ⊤) (hΦinj : ∀ v ∈ parR M Hs ℤ_[p], Φ v = 0 → v = 0) :
    ↥(parR M Hs ℤ_[p]) ≃ₗ[ℤ_[p]] (T →ₗ[ℤ_[p]] ℤ_[p]) :=
  LinearEquiv.ofBijective (Φ ∘ₗ (parR M Hs ℤ_[p]).subtype) ⟨by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hΦinj v v.2 hv), by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype, hΦsurj]⟩

theorem eΦ_apply (v : ↥(parR M Hs ℤ_[p])) : eΦ M Hs p T Φ hΦsurj hΦinj v = Φ (v : H1 M Hs ℤ_[p]) := rfl

def fB : Module.Basis (Fin n) ℤ_[p] (T →ₗ[ℤ_[p]] ℤ_[p]) := bp.map (eΦ M Hs p T Φ hΦsurj hΦinj)

theorem fB_apply (j : Fin n) : fB M Hs p T Φ hΦsurj hΦinj bp j = Φ (bp j : H1 M Hs ℤ_[p]) := by
  rw [fB, Module.Basis.map_apply, eΦ_apply]

def E₀ : T ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
  (Module.evalEquiv ℤ_[p] T).trans (fB M Hs p T Φ hΦsurj hΦinj bp).dualBasis.equivFun

theorem E₀_apply (x : T) (j : Fin n) :
    E₀ M Hs p T Φ hΦsurj hΦinj bp x j = Φ (bp j : H1 M Hs ℤ_[p]) x := by
  classical
  simp only [E₀, LinearEquiv.trans_apply, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr,
    fB_apply]
  rfl

def tB : Module.Basis (Fin n) ℤ_[p] T := Module.Basis.ofEquivFun (E₀ M Hs p T Φ hΦsurj hΦinj bp)

include hΦeq hbp in

theorem toMatrix_tB (g : Gen M S) :
    LinearMap.toMatrix (tB M Hs p T Φ hΦsurj hΦinj bp) (tB M Hs p T Φ hΦsurj hΦinj bp) (G g) =
      ((Mint b S (idx M S g)).transpose).map (Int.cast : ℤ → ℤ_[p]) := by
  classical

  have hE : ∀ (x : T) (j : Fin n), E₀ M Hs p T Φ hΦsurj hΦinj bp (G g x) j =
      ∑ i, ((Mint b S (idx M S g) i j : ℤ) : ℤ_[p]) * E₀ M Hs p T Φ hΦsurj hΦinj bp x i := by
    intro x j
    rw [E₀_apply]
    have h1 : Φ (bp j : H1 M Hs ℤ_[p]) (G g x) = Φ (opFamily M Hs S ℤ_[p] g (bp j : H1 M Hs ℤ_[p])) x := by
      rw [hΦeq g _ (bp j).2]; rfl
    rw [h1, opFamily_apply_eq]
    have hexp : TparI M Hs S ℤ_[p] (idx M S g) (bp j) =
        ∑ i, (LinearMap.toMatrix bp bp (TparI M Hs S ℤ_[p] (idx M S g)) i j) • bp i := by
      conv_lhs => rw [← bp.sum_repr (TparI M Hs S ℤ_[p] (idx M S g) (bp j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.toMatrix_apply]
    rw [hexp, toMatrix_TparI b bp hbp]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, LinearMap.coe_sum,
      Finset.sum_apply, LinearMap.smul_apply, Matrix.map_apply, smul_eq_mul, E₀_apply]
  ext i j
  rw [LinearMap.toMatrix_apply, tB, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]
  rw [hE]
  simp only [LinearEquiv.apply_symm_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i' _ hi'; simp [hi']
  · intro h; exact absurd (Finset.mem_univ j) h

def E : ℚ_[p] ⊗[ℤ_[p]] T ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (Algebra.TensorProduct.basis ℚ_[p] (tB M Hs p T Φ hΦsurj hΦinj bp)).equivFun

include hΦeq hbp in

theorem E_equivariant (g : Gen M S) (v : ℚ_[p] ⊗[ℤ_[p]] T) :
    E M Hs p T Φ hΦsurj hΦinj bp ((G g).baseChange ℚ_[p] v) =
      (((Mint b S (idx M S g)).transpose).map (Int.cast : ℤ → ℚ_[p])).mulVec
        (E M Hs p T Φ hΦsurj hΦinj bp v) := by
  classical
  have h := LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis ℚ_[p] (tB M Hs p T Φ hΦsurj hΦinj bp))
    (Algebra.TensorProduct.basis ℚ_[p] (tB M Hs p T Φ hΦsurj hΦinj bp)) ((G g).baseChange ℚ_[p]) v
  rw [LinearMap.toMatrix_baseChange, toMatrix_tB M Hs S p T G Φ hΦeq hΦsurj hΦinj b bp hbp,
    Matrix.map_map] at h
  simp only [E, Module.Basis.equivFun_apply]
  rw [← h]
  congr 1

end Tate

section Glue

variable {K V T G : Type*} [Field K] [AddCommGroup V] [Module K V] [CommRing T] [Algebra K T]

def lsmulPi : T →ₐ[K] Module.End K (Fin 2 → T) :=
  Algebra.lsmul K K (Fin 2 → T)

@[scoped simp] theorem lsmulPi_apply (s : T) (f : Fin 2 → T) : lsmulPi (K := K) s f = s • f := rfl

def theta (e : V ≃ₗ[K] (Fin 2 → T)) : T →ₐ[K] Module.End K V :=
  ((LinearEquiv.conjAlgEquiv K e.symm).toAlgHom).comp (lsmulPi (K := K))

theorem theta_apply (e : V ≃ₗ[K] (Fin 2 → T)) (s : T) (v : V) :
    theta e s v = e.symm (s • e v) := by
  simp [theta, LinearEquiv.conjAlgEquiv_apply]

theorem e_theta (e : V ≃ₗ[K] (Fin 2 → T)) (s : T) (v : V) :
    e (theta e s v) = s • e v := by
  rw [theta_apply, LinearEquiv.apply_symm_apply]

theorem theta_injective (e : V ≃ₗ[K] (Fin 2 → T)) : Function.Injective (theta e) := by
  intro s s' h
  have := congrArg (fun f : Module.End K V => e (f (e.symm (fun _ => (1 : T))))) h
  simp only [theta_apply, LinearEquiv.apply_symm_apply] at this
  have h0 := congrFun this 0
  simpa using h0

variable (ρ : G → Module.End K V) (φ : G → T)

theorem theta_range_eq (e : V ≃ₗ[K] (Fin 2 → T))
    (hφ : Algebra.adjoin K (Set.range φ) = ⊤)
    (he : ∀ t v, e (ρ t v) = φ t • e v) :
    (theta e).range = Algebra.adjoin K (Set.range ρ) := by
  have hθφ : ∀ t, theta e (φ t) = ρ t := by
    intro t
    refine LinearMap.ext fun v => ?_
    rw [theta_apply, ← he, LinearEquiv.symm_apply_apply]
  rw [← Algebra.map_top, ← hφ, AlgHom.map_adjoin]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (hθφ t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨φ t, ⟨t, rfl⟩, hθφ t⟩

def thetaEquiv (e : V ≃ₗ[K] (Fin 2 → T))
    (hφ : Algebra.adjoin K (Set.range φ) = ⊤)
    (he : ∀ t v, e (ρ t v) = φ t • e v) :
    T ≃ₐ[K] Algebra.adjoin K (Set.range ρ) :=
  (AlgEquiv.ofInjective (theta e) (theta_injective e)).trans
    (Subalgebra.equivOfEq _ _ (theta_range_eq ρ φ e hφ he))

def basisEquiv (e : V ≃ₗ[K] (Fin 2 → T))
    (hφ : Algebra.adjoin K (Set.range φ) = ⊤)
    (he : ∀ t v, e (ρ t v) = φ t • e v) :
    V ≃ₗ[Algebra.adjoin K (Set.range ρ)] (Fin 2 → Algebra.adjoin K (Set.range ρ)) :=
  let θ := thetaEquiv ρ φ e hφ he
  { toFun := fun v i => θ (e v i)
    invFun := fun g => e.symm (fun i => θ.symm (g i))
    map_add' := fun v w => by
      funext i
      simp only [map_add, Pi.add_apply]
    map_smul' := fun a v => by
      funext i
      simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
      obtain ⟨s, rfl⟩ := θ.surjective a
      rw [← map_mul]
      congr 1
      have h1 : ((θ s : Algebra.adjoin K (Set.range ρ)) • v) = theta e s v := rfl
      rw [h1, e_theta, Pi.smul_apply, smul_eq_mul]
    left_inv := fun v => by
      simp only [AlgEquiv.symm_apply_apply]
      exact e.symm_apply_apply v
    right_inv := fun g => by
      funext i
      simp only [LinearEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] }

theorem nonempty_basis (e : V ≃ₗ[K] (Fin 2 → T))
    (hφ : Algebra.adjoin K (Set.range φ) = ⊤)
    (he : ∀ t v, e (ρ t v) = φ t • e v) :
    Nonempty (Module.Basis (Fin 2) (Algebra.adjoin K (Set.range ρ)) V) :=
  ⟨Module.Basis.ofEquivFun (basisEquiv ρ φ e hφ he)⟩

end Glue

section Coord

variable (p : ℕ) [Fact p.Prime] {ι : Type} {n : ℕ} (N : ι → Matrix (Fin n) (Fin n) ℚ_[p])

abbrev Tp : Subalgebra ℚ_[p] (Matrix (Fin n) (Fin n) ℚ_[p]) := Algebra.adjoin ℚ_[p] (Set.range N)

def ψ (w : Fin 2 → Fin n → ℚ_[p]) : (Fin 2 → Tp p N) →ₗ[ℚ_[p]] (Fin n → ℚ_[p]) where
  toFun s := ∑ a, ((s a : Tp p N) : Matrix (Fin n) (Fin n) ℚ_[p]).mulVec (w a)
  map_add' s s' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.add_mulVec, Finset.sum_add_distrib]
  map_smul' r s := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.smul_mulVec, RingHom.id_apply,
      Finset.smul_sum]

theorem ψ_equivariant (w : Fin 2 → Fin n → ℚ_[p]) (a : Tp p N) (s : Fin 2 → Tp p N) :
    ψ p N w (a • s) = (a : Matrix (Fin n) (Fin n) ℚ_[p]).mulVec (ψ p N w s) := by
  simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, Subalgebra.coe_mul,
    Matrix.mulVec_sum, Matrix.mulVec_mulVec]

theorem exists_equiv (w : Fin 2 → Fin n → ℚ_[p]) (hw : Function.Bijective (ψ p N w)) :
    ∃ e : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → Tp p N),
      ∀ (i : ι) (z : Fin n → ℚ_[p]), e ((N i).mulVec z) =
        (⟨N i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ : Tp p N) • e z := by
  let e := (LinearEquiv.ofBijective (ψ p N w) hw).symm
  refine ⟨e, fun i z => ?_⟩
  apply e.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (N i).mulVec z = ψ p N w (_ • e z)
  rw [ψ_equivariant]
  congr 1
  exact ((LinearEquiv.ofBijective (ψ p N w) hw).apply_symm_apply z).symm

theorem adjoin_range_gens {G : Type*} (f : G → ι) (hf : Function.Surjective f) :
    Algebra.adjoin ℚ_[p] (Set.range fun g : G =>
      (⟨N (f g), Algebra.subset_adjoin (Set.mem_range_self (f g))⟩ : Tp p N)) = ⊤ := by
  apply Subalgebra.map_injective (f := (Tp p N).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
  have : ((Tp p N).val : Tp p N → Matrix (Fin n) (Fin n) ℚ_[p]) ∘ (fun g : G =>
      (⟨N (f g), Algebra.subset_adjoin (Set.mem_range_self (f g))⟩ : Tp p N)) = N ∘ f := by
    funext g; rfl
  rw [this, Set.range_comp, hf.range_eq, Set.image_univ]

end Coord

section Final

open CongruenceSubgroup CohCarrier ModularCurve ModularCurve.Period Matrix
open scoped TensorProduct IsMulCommutative

theorem main_abstract (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite)
    (p : ℕ) [Fact p.Prime]
    (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (G : Gen M S → Module.End ℤ_[p] T)
    (Φ : H1 M H ℤ_[p] →ₗ[ℤ_[p]] (T →ₗ[ℤ_[p]] ℤ_[p]))
    (hΦeq : ∀ (g : Gen M S) (v : H1 M H ℤ_[p]), v ∈ parR M H ℤ_[p] →
      Φ (opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ G g)
    (hΦsurj : (parR M H ℤ_[p]).map Φ = ⊤)
    (hΦinj : ∀ v ∈ parR M H ℤ_[p], Φ v = 0 → v = 0) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : Gen M S => (G g).baseChange ℚ_[p]))
      (ℚ_[p] ⊗[ℤ_[p]] T)) := by
  classical

  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH M H)
  obtain ⟨bp, hbp⟩ := hb ℤ_[p]
  obtain ⟨bC, hbC⟩ := hb ℂ

  obtain ⟨w, hw⟩ := rowfree M H S hSfin b bC hbC ℚ_[p]

  let N : Idx M S → Matrix (Fin n) (Fin n) ℚ_[p] := fun i =>
    ((Mint b S i).transpose).map (Int.cast : ℤ → ℚ_[p])
  have hw' : Function.Bijective (ψ p N w) := hw
  obtain ⟨e₂, he₂⟩ := exists_equiv p N w hw'

  let E1 := E M H p T Φ hΦsurj hΦinj bp
  have hE1 : ∀ (g : Gen M S) (v : ℚ_[p] ⊗[ℤ_[p]] T),
      E1 ((G g).baseChange ℚ_[p] v) = (N (idx M S g)).mulVec (E1 v) :=
    fun g v => E_equivariant M H S p T G Φ hΦeq hΦsurj hΦinj b bp hbp g v

  haveI : IsMulCommutative (Tp p N) := Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    change ((Int.castRingHom ℚ_[p]).mapMatrix (Mint b S i)ᵀ) *
        ((Int.castRingHom ℚ_[p]).mapMatrix (Mint b S j)ᵀ) =
      ((Int.castRingHom ℚ_[p]).mapMatrix (Mint b S j)ᵀ) *
        ((Int.castRingHom ℚ_[p]).mapMatrix (Mint b S i)ᵀ)
    rw [← map_mul, ← map_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, Mint_comm])

  let φ : Gen M S → Tp p N := fun g =>
    ⟨N (idx M S g), Algebra.subset_adjoin (Set.mem_range_self _)⟩
  have hφ : Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ :=
    adjoin_range_gens p N (idx M S) (idx_surjective M S)
  have he : ∀ (g : Gen M S) (v : ℚ_[p] ⊗[ℤ_[p]] T),
      (E1.trans e₂) ((fun g : Gen M S => (G g).baseChange ℚ_[p]) g v) = φ g • (E1.trans e₂) v := by
    intro g v
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    change e₂ (E1 ((G g).baseChange ℚ_[p] v)) = _
    rw [hE1, he₂]
  exact nonempty_basis (fun g : Gen M S => (G g).baseChange ℚ_[p]) φ (E1.trans e₂) hφ he

end Final

end RTJH
p2m_reactivate "P2MW.S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH.RTJH"

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) =>
          (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) :=
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
    (ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH M p H).1
  haveI : Module.Free ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
    (ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH M p H).2
  RTJH.main_abstract M H (↑S : Set ℕ) S.finite_toSet p (TateModule p (ModularCurve.JH M H))
    (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)
    (ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH M p H (↑S : Set ℕ) hin).choose
    (ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH M p H (↑S : Set ℕ)
      hin).choose_spec.1
    (ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH M p H (↑S : Set ℕ)
      hin).choose_spec.2.1
    (ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH M p H (↑S : Set ℕ)
      hin).choose_spec.2.2

end
p2m_reactivate "P2MW.S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH.RTJH"

end S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH
end P2MW
export P2MW.S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH (solution)
