-- Prove2me | solution 1 for ModularCurve.exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b99cda9f-17b1-55c8-8b79-93f50ae7162e

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups

namespace HeckeCompatRed

section Alg

variable {K : Type*} [CommRing K] {𝕋 : Type*} [CommRing 𝕋] [Algebra K 𝕋] {G : Type*} (ops : G → 𝕋)

theorem exists_ringHom_of_injective (hgen : Algebra.adjoin K (Set.range ops) = ⊤)
    {D : Type*} [Ring D] [Algebra K D] (σ : 𝕋 →ₐ[K] D)
    {P : Type*} [Ring P] [Algebra K P] (Ξ : P →ₐ[K] D) (hΞ : Function.Injective Ξ)
    (x : G → P) (hx : ∀ g, Ξ (x g) = σ (ops g))
    {E : Type*} [NonAssocSemiring E] (θ : P →+* E) :
    ∃ τ : 𝕋 →+* E, ∀ g, τ (ops g) = θ (x g) := by
  have hmem : ∀ t : 𝕋, σ t ∈ Ξ.range := by
    have hle : Algebra.adjoin K (Set.range ops) ≤ Ξ.range.comap σ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨g, rfl⟩
      exact (Subalgebra.mem_comap _ _ _).2 ⟨x g, hx g⟩
    intro t
    have ht : t ∈ Algebra.adjoin K (Set.range ops) := hgen ▸ Algebra.mem_top
    exact (Subalgebra.mem_comap _ _ _).1 (hle ht)
  let ε : 𝕋 →ₐ[K] P :=
    (AlgEquiv.ofInjective Ξ hΞ).symm.toAlgHom.comp (σ.codRestrict Ξ.range hmem)
  refine ⟨θ.comp ε.toRingHom, fun g => ?_⟩
  have h1 : σ.codRestrict Ξ.range hmem (ops g) = AlgEquiv.ofInjective Ξ hΞ (x g) :=
    Subtype.ext (by rw [AlgHom.coe_codRestrict, AlgEquiv.ofInjective_apply, hx])
  show θ (ε (ops g)) = θ (x g)
  congr 1
  show (AlgEquiv.ofInjective Ξ hΞ).symm (σ.codRestrict Ξ.range hmem (ops g)) = x g
  rw [h1, AlgEquiv.symm_apply_apply]

end Alg

section BaseChange

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]
  {Λ : Type*} [AddCommGroup Λ] [Module R Λ]

theorem liftBaseChange_comp (χ : Λ →ₗ[R] K) (Q : Λ →ₗ[R] Λ) :
    (χ ∘ₗ Q).liftBaseChange K = χ.liftBaseChange K ∘ₗ Q.baseChange K := by
  refine TensorProduct.AlgebraTensorModule.ext fun a l => ?_
  rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearMap.liftBaseChange_tmul]

theorem eq_of_forall_liftBaseChange_eq [Module.Free R Λ] {y y' : K ⊗[R] Λ}
    (h : ∀ χ : Λ →ₗ[R] K, χ.liftBaseChange K y = χ.liftBaseChange K y') : y = y' := by
  let b := Module.Free.chooseBasis R Λ
  let bK := Algebra.TensorProduct.basis K b
  refine bK.ext_elem_iff.2 fun i => ?_
  have hco : ∀ z, bK.repr z i = ((Algebra.linearMap R K) ∘ₗ b.coord i).liftBaseChange K z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    | tmul a l =>
        rw [Algebra.TensorProduct.basis_repr_tmul, LinearMap.liftBaseChange_tmul, Finsupp.smul_apply,
          Finsupp.mapRange_apply, LinearMap.comp_apply, Algebra.linearMap_apply, Module.Basis.coord_apply]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  rw [hco, hco, h]

end BaseChange

section Comparison

variable (R : Type*) [CommRing R] (K : Type*) [CommRing K] [Algebra R K]
  (Λ : Type*) [AddCommGroup Λ] [Module R Λ]

def bcHom : Module.End R Λ →ₐ[R] Module.End K (K ⊗[R] Λ) where
  toFun Q := Q.baseChange K
  map_one' := LinearMap.baseChange_one R Λ
  map_mul' f g := LinearMap.baseChange_mul f g
  map_zero' := LinearMap.baseChange_zero
  map_add' f g := LinearMap.baseChange_add f g
  commutes' r := TensorProduct.AlgebraTensorModule.ext fun a l => by
    rw [LinearMap.baseChange_tmul, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]

@[scoped simp] theorem bcHom_apply (Q : Module.End R Λ) : bcHom R K Λ Q = Q.baseChange K := rfl

variable {R Λ} {Rc : Type*} [Ring Rc] [Algebra R Rc]

def Xi (ι : Rc →ₐ[R] Module.End R Λ) : K ⊗[R] Rc →ₐ[K] Module.End K (K ⊗[R] Λ) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) ((bcHom R K Λ).comp ι)
    (fun a y => Algebra.commute_algebraMap_left a _)

theorem Xi_tmul (ι : Rc →ₐ[R] Module.End R Λ) (a : K) (r : Rc) :
    Xi K ι (a ⊗ₜ r) = a • (ι r).baseChange K := by
  rw [Xi, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
  rfl

theorem Xi_injective [Module.Flat R K] [Module.Free R Λ] [Module.Finite R Λ]
    (ι : Rc →ₐ[R] Module.End R Λ) (hι : Function.Injective ι) : Function.Injective (Xi K ι) := by
  classical
  let b := Module.Free.chooseBasis R Λ
  haveI : Fintype (Module.Free.ChooseBasisIndex R Λ) := Module.Free.ChooseBasisIndex.fintype R Λ
  let ev : Module.End R Λ →ₗ[R] (Module.Free.ChooseBasisIndex R Λ → Λ) :=
    LinearMap.pi fun i => LinearMap.applyₗ (b i)
  have hev : Function.Injective ev := by
    intro Q Q' h
    exact b.ext fun i => congr_fun h i
  have hflat : Function.Injective ((ev ∘ₗ ι.toLinearMap).lTensor K) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (hev.comp hι)
  let F : K ⊗[R] Rc → (Module.Free.ChooseBasisIndex R Λ → K ⊗[R] Λ) := fun z =>
    TensorProduct.piRight R K K (fun _ : Module.Free.ChooseBasisIndex R Λ => Λ)
      ((ev ∘ₗ ι.toLinearMap).lTensor K z)
  have hF : Function.Injective F :=
    (TensorProduct.piRight R K K (fun _ : Module.Free.ChooseBasisIndex R Λ => Λ)).injective.comp hflat
  have hFXi : ∀ z i, F z i = Xi K ι z ((1 : K) ⊗ₜ b i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp only [F, map_zero, Pi.zero_apply, LinearMap.zero_apply]
    | tmul a r =>
        simp only [F, LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
          Xi_tmul, LinearMap.smul_apply, LinearMap.baseChange_tmul]
        show a ⊗ₜ[R] (ι r) (b i) = a • ((1 : K) ⊗ₜ[R] (ι r) (b i))
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add u v hu hv =>
        simp only [F, map_add, Pi.add_apply, LinearMap.add_apply] at hu hv ⊢
        rw [hu, hv]
  intro z z' h
  apply hF
  funext i
  rw [hFXi, hFXi, h]

theorem exists_ringHom_of_tensor [Module.Flat R K] [Module.Free R Λ] [Module.Finite R Λ]
    {V : Type*} [AddCommGroup V] [Module K V] (e : V ≃ₗ[K] K ⊗[R] Λ)
    {𝕋 : Type*} [CommRing 𝕋] [Algebra K 𝕋] [Module 𝕋 V] [IsScalarTower K 𝕋 V]
    {G : Type*} (ops : G → 𝕋) (hgen : Algebra.adjoin K (Set.range ops) = ⊤)
    (ι : Rc →ₐ[R] Module.End R Λ) (hι : Function.Injective ι) (Tf : G → Rc)
    (hkey : ∀ (g : G) (v : V), e (ops g • v) = (ι (Tf g)).baseChange K (e v))
    {E : Type*} [NonAssocSemiring E] (θ : K ⊗[R] Rc →+* E) :
    ∃ τ : 𝕋 →+* E, ∀ g, τ (ops g) = θ ((1 : K) ⊗ₜ Tf g) := by
  haveI : SMulCommClass 𝕋 K V := SMulCommClass.symm K 𝕋 V
  let act : 𝕋 →ₐ[K] Module.End K V := Algebra.lsmul K K V
  let σ : 𝕋 →ₐ[K] Module.End K (K ⊗[R] Λ) := (LinearEquiv.conjAlgEquiv K e).toAlgHom.comp act
  refine exists_ringHom_of_injective ops hgen (D := Module.End K (K ⊗[R] Λ)) σ (Xi K ι) (Xi_injective K ι hι)
    (fun g => (1 : K) ⊗ₜ Tf g) (fun g => ?_) θ
  rw [Xi_tmul, one_smul]
  refine LinearMap.ext fun w => ?_
  have hσ : σ (ops g) w = e (ops g • e.symm w) := by
    show (LinearEquiv.conjAlgEquiv K e) (act (ops g)) w = _
    rw [LinearEquiv.conjAlgEquiv_apply]
    rfl
  rw [hσ, hkey, LinearEquiv.apply_symm_apply]

end Comparison

section Naturality

open CohCarrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem heckeT_apply_eq_sum (φ : H1 M H A) (u : ↥(GammaH M H))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M H) ⧸ GammaHUpper M H ℓ)))] :
    heckeT M H ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M H) ⧸ GammaHUpper M H ℓ)),
        φ (Additive.ofMul (conjL M H ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem heckeT_comp (h : A →+ B) (φ : H1 M H A) :
    heckeT M H ℓ B (h.comp φ) = h.comp (heckeT M H ℓ A φ) := by
  classical
  refine AddMonoidHom.ext fun a => ?_
  set u := Additive.toMul a with hu
  have ha : a = Additive.ofMul u := rfl
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M H) ⧸ GammaHUpper M H ℓ))) := Fintype.ofFinite _
  rw [ha, AddMonoidHom.comp_apply, heckeT_apply_eq_sum, heckeT_apply_eq_sum, map_sum]
  rfl

omit [NeZero ℓ] in

theorem diamondRaw_comp (σ : CongruenceSubgroup.Gamma0 M) (h : A →+ B) (φ : H1 M H A) :
    diamondRaw M H B σ (h.comp φ) = h.comp (diamondRaw M H A σ φ) :=
  AddMonoidHom.ext fun _ => rfl

end Naturality

section PeriodSide

open CohCarrier ModularCurve

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem isCongruenceSubgroup_gammaH : CongruenceSubgroup.IsCongruenceSubgroup (GammaH M H) :=
  ⟨M, NeZero.ne M, CuspForm.Gamma_le_GammaH M H⟩

abbrev Lat : Submodule ℤ (Module.Dual ℂ (CuspForm (GammaH M H) 2)) := periodLatticeOf (GammaH M H)

def perL (δ : ↥(GammaH M H)) : ↥(Lat M H) :=
  ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩

@[scoped simp] theorem coe_perL (δ : ↥(GammaH M H)) :
    ((perL M H δ : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) = periodOf (GammaH M H) δ := rfl

theorem periodOf_mul (γ δ : ↥(GammaH M H)) :
    periodOf (GammaH M H) (γ * δ) = periodOf (GammaH M H) γ + periodOf (GammaH M H) δ := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.add_apply, ← periodMapOf_apply_eq_periodOf, ← periodMapOf_apply_eq_periodOf,
    ← periodMapOf_apply_eq_periodOf, ofMul_mul, map_add]

theorem periodOf_one : periodOf (GammaH M H) 1 = 0 := by
  have h := periodOf_mul M H 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem periodOf_eq_zero_of_trace (δ : ↥(GammaH M H))
    (hδ : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : periodOf (GammaH M H) δ = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [← periodMapOf_apply_eq_periodOf, LinearMap.zero_apply]
  exact (Period.mem_parabolicHoms_iff.1 (periodMapOf_mem_parabolicHoms (GammaH M H) f)) δ hδ

def perHom : H1 M H ↥(Lat M H) where
  toFun a := perL M H (Additive.toMul a)
  map_zero' := Subtype.ext (periodOf_one M H)
  map_add' a b := Subtype.ext (periodOf_mul M H (Additive.toMul a) (Additive.toMul b))

@[scoped simp] theorem perHom_apply (δ : ↥(GammaH M H)) : perHom M H (Additive.ofMul δ) = perL M H δ := rfl

theorem comp_perHom_mem_parabolicHoms {A : Type*} [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (χ : ↥(Lat M H) →+ A) : χ.comp (perHom M H) ∈ Period.parabolicHoms R (GammaH M H) A := by
  refine Period.mem_parabolicHoms_iff.2 fun δ hδ => ?_
  rw [AddMonoidHom.comp_apply, perHom_apply]
  have : perL M H δ = 0 := Subtype.ext (periodOf_eq_zero_of_trace M H δ hδ)
  rw [this, map_zero]

def evalL (f : CuspForm (GammaH M H) 2) : ↥(Lat M H) →+ ℂ where
  toFun v := (v : Module.Dual ℂ (CuspForm (GammaH M H) 2)) f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalL_comp_perHom (f : CuspForm (GammaH M H) 2) :
    (evalL M H f).comp (perHom M H) = periodMapOf (GammaH M H) f := by
  ext a
  show periodOf (GammaH M H) (Additive.toMul a) f = periodMapOf (GammaH M H) f a
  rw [← periodMapOf_apply_eq_periodOf]
  rfl

theorem periodMapOf_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (GammaH M H) 2) :
    periodMapOf (GammaH M H) (CuspForm.heckeTLinH 2 hℓ hℓM f) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ℂ (periodMapOf (GammaH M H) f)) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM) f _
    (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

theorem periodMapOf_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (GammaH M H) 2) :
    periodMapOf (GammaH M H) (CuspForm.heckeULinH 2 q f) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT M H q ℂ (periodMapOf (GammaH M H) f)) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU M H hq hqM f _
    (CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f)

theorem periodMapOf_diamondLinH (d : (ZMod M)ˣ) (f : CuspForm (GammaH M H) 2) :
    periodMapOf (GammaH M H) (CuspForm.diamondLinH 2 d f) =
      diamondRaw M H ℂ (CuspForm.gammaLift M d) (periodMapOf (GammaH M H) f) :=
  periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H (CuspForm.gammaLift M d) f _
    (CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) d f)

theorem dualMap_heckeTLinH_periodOf {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (δ : ↥(GammaH M H)) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap (periodOf (GammaH M H) δ) =
      (((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ↥(Lat M H) (perHom M H)) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_heckeTLinH,
    ← evalL_comp_perHom, heckeT_comp]
  rfl

theorem dualMap_heckeULinH_periodOf {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (δ : ↥(GammaH M H)) :
    (CuspForm.heckeULinH 2 q).dualMap (periodOf (GammaH M H) δ) =
      (((haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT M H q ↥(Lat M H) (perHom M H)) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_heckeULinH M H hq hqM,
    ← evalL_comp_perHom, heckeT_comp]
  rfl

theorem dualMap_diamondLinH_periodOf (d : (ZMod M)ˣ) (δ : ↥(GammaH M H)) :
    (CuspForm.diamondLinH 2 d).dualMap (periodOf (GammaH M H) δ) =
      ((diamondRaw M H ↥(Lat M H) (CuspForm.gammaLift M d) (perHom M H) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_diamondLinH,
    ← evalL_comp_perHom, diamondRaw_comp]
  rfl

theorem dualMap_mem_of_forall {T : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2}
    (hT : ∀ δ : ↥(GammaH M H), T.dualMap (periodOf (GammaH M H) δ) ∈ Lat M H) :
    ∀ v ∈ Lat M H, T.dualMap v ∈ Lat M H := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    exact hT δ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

variable (S : Set ℕ)

theorem dualMap_heckeGenH_mem (g : Gen M S) :
    ∀ v ∈ Lat M H, (CuspForm.heckeGenH (H := H) S 2 g).dualMap v ∈ Lat M H := by
  refine dualMap_mem_of_forall M H fun δ => ?_
  cases g with
  | T ℓ hℓ hℓS hℓM => rw [CuspForm.heckeGenH_T, dualMap_heckeTLinH_periodOf]; exact Subtype.mem _
  | U q hq hqM => rw [CuspForm.heckeGenH_U, dualMap_heckeULinH_periodOf M H hq hqM]; exact Subtype.mem _
  | dia d => rw [CuspForm.heckeGenH_dia, dualMap_diamondLinH_periodOf]; exact Subtype.mem _

theorem dualMap_mem_of_mem_heckeRingH {t : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2}
    (ht : t ∈ CuspForm.heckeRingH M H 2) : ∀ v ∈ Lat M H, t.dualMap v ∈ Lat M H := by
  induction ht using Subring.closure_induction with
  | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact dualMap_heckeGenH_mem M H ∅ g
  | zero =>
      intro v hv
      have h0 : (0 : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2).dualMap v = 0 :=
        LinearMap.ext fun f => by rw [LinearMap.dualMap_apply, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
      rw [h0]
      exact zero_mem _
  | one =>
      intro v hv
      have h1 : (1 : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2).dualMap v = v :=
        LinearMap.ext fun f => rfl
      rw [h1]
      exact hv
  | add x y _ _ hx hy =>
      intro v hv
      have h2 : (x + y).dualMap v = x.dualMap v + y.dualMap v :=
        LinearMap.ext fun f => by
          rw [LinearMap.dualMap_apply, LinearMap.add_apply, LinearMap.add_apply, map_add,
            LinearMap.dualMap_apply, LinearMap.dualMap_apply]
      rw [h2]
      exact add_mem (hx v hv) (hy v hv)
  | neg x _ hx =>
      intro v hv
      have h3 : (-x).dualMap v = -(x.dualMap v) :=
        LinearMap.ext fun f => by
          rw [LinearMap.dualMap_apply, LinearMap.neg_apply, LinearMap.neg_apply, map_neg, LinearMap.dualMap_apply]
      rw [h3]
      exact neg_mem (hx v hv)
  | mul x y _ _ hx hy =>
      intro v hv
      have h4 : (x * y).dualMap v = y.dualMap (x.dualMap v) := LinearMap.ext fun f => rfl
      rw [h4]
      exact hy _ (hx v hv)

def dualRes (t : CuspForm.heckeRingH M H 2) : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  (((t : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2).dualMap).restrictScalars ℤ).restrict
    (dualMap_mem_of_mem_heckeRingH M H t.2)

theorem coe_dualRes (t : CuspForm.heckeRingH M H 2) (l : ↥(Lat M H)) :
    ((dualRes M H t l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
      (t : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2).dualMap l := rfl

theorem dualRes_apply_apply (t : CuspForm.heckeRingH M H 2) (l : ↥(Lat M H)) (f : CuspForm (GammaH M H) 2) :
    ((dualRes M H t l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) f =
      (l : Module.Dual ℂ (CuspForm (GammaH M H) 2)) ((t : CuspForm (GammaH M H) 2 →ₗ[ℂ] _) f) := rfl

def iotaR : (CuspForm.heckeRingH M H 2)ᵐᵒᵖ →+* Module.End ℤ ↥(Lat M H) where
  toFun T := dualRes M H (MulOpposite.unop T)
  map_one' := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun f => rfl)
  map_mul' T T' := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun f => rfl)
  map_zero' := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun f => by
    rw [dualRes_apply_apply]
    exact map_zero (l : Module.Dual ℂ (CuspForm (GammaH M H) 2)))
  map_add' T T' := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun f => by
    show ((dualRes M H (MulOpposite.unop T + MulOpposite.unop T') l : ↥(Lat M H)) : Module.Dual ℂ _) f =
      ((dualRes M H (MulOpposite.unop T) l : ↥(Lat M H)) : Module.Dual ℂ _) f +
        ((dualRes M H (MulOpposite.unop T') l : ↥(Lat M H)) : Module.Dual ℂ _) f
    rw [dualRes_apply_apply, dualRes_apply_apply, dualRes_apply_apply]
    exact map_add (l : Module.Dual ℂ (CuspForm (GammaH M H) 2)) _ _)

theorem iotaR_apply (T : (CuspForm.heckeRingH M H 2)ᵐᵒᵖ) : iotaR M H T = dualRes M H (MulOpposite.unop T) := rfl

theorem eq_zero_of_dualMap_eq_zero (t : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2)
    (hΛ : ∀ v ∈ Lat M H, t.dualMap v = 0) : t = 0 := by
  obtain ⟨n, b, -, hsp⟩ :=
    exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH M H) (isCongruenceSubgroup_gammaH M H)
  have hall : ∀ v : Module.Dual ℂ (CuspForm (GammaH M H) 2), t.dualMap v = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range fun i => ((b i : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2))) :=
      hsp ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hΛ _ (b i).2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [LinearMap.map_smul_of_tower, hx, smul_zero]
  refine LinearMap.ext fun f => ?_
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (t f)).1 fun φ => ?_
  have := LinearMap.congr_fun (hall φ) f
  rwa [LinearMap.dualMap_apply, LinearMap.zero_apply] at this

theorem iotaR_injective : Function.Injective (iotaR M H) := by
  intro T T' h
  apply MulOpposite.unop_injective
  rw [← sub_eq_zero]
  refine Subtype.ext ?_
  rw [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero]
  refine eq_zero_of_dualMap_eq_zero M H _ fun v hv => ?_
  have h' : ((iotaR M H T ⟨v, hv⟩ : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
      ((iotaR M H T' ⟨v, hv⟩ : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by rw [h]
  refine LinearMap.ext fun f => ?_
  have hf := LinearMap.congr_fun h' f
  rw [iotaR_apply, iotaR_apply, dualRes_apply_apply, dualRes_apply_apply] at hf
  rw [LinearMap.dualMap_apply, LinearMap.sub_apply, map_sub, LinearMap.zero_apply, sub_eq_zero]
  exact hf

variable {p : ℕ} [Fact p.Prime]

abbrev genR (g : Gen M S) : CuspForm.heckeRingH M H 2 :=
  ⟨CuspForm.heckeGenH S 2 g, CuspForm.heckeGenH_mem_heckeRingH S 2 g⟩

theorem chi_dualRes_perL (g : Gen M S) (ψ : H1 M H ℤ_[p]) (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ)) (δ : ↥(GammaH M H)) :
    χ (dualRes M H (genR M H S g) (perL M H δ)) = opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ) := by
  have hcomp : χ.toAddMonoidHom.comp (perHom M H) = ψ := by
    ext a
    exact hχ (Additive.toMul a)
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hval : dualRes M H (genR M H S (.T ℓ hℓ hℓS hℓM)) (perL M H δ) =
        heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
      Subtype.ext (dualMap_heckeTLinH_periodOf M H hℓ hℓM δ)
    rw [hval]
    show χ.toAddMonoidHom (heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
    rw [← AddMonoidHom.comp_apply, ← heckeT_comp, hcomp]
    rfl
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hval : dualRes M H (genR M H S (.U q hq hqM)) (perL M H δ) =
        heckeT M H q ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
      Subtype.ext (dualMap_heckeULinH_periodOf M H hq hqM δ)
    rw [hval]
    show χ.toAddMonoidHom (heckeT M H q ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
    rw [← AddMonoidHom.comp_apply, ← heckeT_comp, hcomp]
    rfl
  | dia d =>
    have hval : dualRes M H (genR M H S (.dia d)) (perL M H δ) =
        diamondRaw M H ↥(Lat M H) (CuspForm.gammaLift M d) (perHom M H) (Additive.ofMul δ) :=
      Subtype.ext (dualMap_diamondLinH_periodOf M H d δ)
    rw [hval]
    show χ.toAddMonoidHom (diamondRaw M H ↥(Lat M H) _ (perHom M H) (Additive.ofMul δ)) = _
    rw [← AddMonoidHom.comp_apply, ← diamondRaw_comp, hcomp]
    rfl

theorem key [Module.Free ℤ ↥(Lat M H)]
    (e : TateModule p (JH M H) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥(Lat M H))
    (he : ∀ (g : Gen M S) (ψ : H1 M H ℤ_[p]),
        ψ ∈ Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : ↥(GammaH M H), χ ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : ↥(GammaH M H), χ' ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩ =
              opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) = χ.liftBaseChange ℤ_[p] (e (tateGenOpH M H S p g x)))
    (g : Gen M S) (x : TateModule p (JH M H)) :
    e (tateGenOpH M H S p g x) = (dualRes M H (genR M H S g)).baseChange ℤ_[p] (e x) := by
  refine eq_of_forall_liftBaseChange_eq ℤ_[p] fun χ => ?_
  have h := he g (χ.toAddMonoidHom.comp (perHom M H)) (comp_perHom_mem_parabolicHoms M H ℤ_[p] _)
    χ (χ ∘ₗ dualRes M H (genR M H S g)) (fun δ => rfl)
    (fun δ => chi_dualRes_perL M H S g _ χ (fun _ => rfl) δ) x
  rw [liftBaseChange_comp, LinearMap.comp_apply] at h
  exact h.symm

end PeriodSide

section FormsSide

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (r : ℕ) (A : Subring ℂ) (I : Ideal A)

def rhoR : CuspForm.heckeRingH M H 2 →+* Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 r A I) where
  toFun t := CuspForm.twoCuspEndMod I t
  map_one' := by
    refine LinearMap.ext fun ω => ?_
    obtain ⟨x, rfl⟩ := CuspForm.twoCuspReduce_surjective M H 2 r A I ω
    rw [CuspForm.twoCuspEndMod_reduce, CuspForm.twoCuspEnd_one]
    rfl
  map_mul' t t' := by
    refine LinearMap.ext fun ω => ?_
    obtain ⟨x, rfl⟩ := CuspForm.twoCuspReduce_surjective M H 2 r A I ω
    rw [Module.End.mul_apply, CuspForm.twoCuspEndMod_reduce, CuspForm.twoCuspEndMod_reduce,
      CuspForm.twoCuspEndMod_reduce, CuspForm.twoCuspEnd_mul]
    rfl
  map_zero' := by
    refine LinearMap.ext fun ω => ?_
    obtain ⟨x, rfl⟩ := CuspForm.twoCuspReduce_surjective M H 2 r A I ω
    rw [CuspForm.twoCuspEndMod_reduce, LinearMap.zero_apply]
    have : CuspForm.twoCuspEnd (p := r) (A := A) (0 : CuspForm.heckeRingH M H 2) x = 0 := Subtype.ext rfl
    rw [this, map_zero]
  map_add' t t' := by
    refine LinearMap.ext fun ω => ?_
    obtain ⟨x, rfl⟩ := CuspForm.twoCuspReduce_surjective M H 2 r A I ω
    rw [LinearMap.add_apply, CuspForm.twoCuspEndMod_reduce, CuspForm.twoCuspEndMod_reduce,
      CuspForm.twoCuspEndMod_reduce]
    have : CuspForm.twoCuspEnd (p := r) (A := A) (t + t') x =
        CuspForm.twoCuspEnd t x + CuspForm.twoCuspEnd t' x := Subtype.ext rfl
    rw [this, map_add]

@[scoped simp] theorem rhoR_apply (t : CuspForm.heckeRingH M H 2) : rhoR M H r A I t = CuspForm.twoCuspEndMod I t := rfl

variable {p : ℕ} [Fact p.Prime]

def padicToQuot (hpI : (p : A) ∈ I) : ℤ_[p] →+* A ⧸ I :=
  haveI hdvd : ringChar (A ⧸ I) ∣ p := (ringChar.spec (A ⧸ I) p).1 (by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hpI)
  (ZMod.castHom hdvd (A ⧸ I)).comp PadicInt.toZMod

def padicToEndOp (hpI : (p : A) ∈ I) :
    ℤ_[p] →+* (Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 r A I))ᵐᵒᵖ :=
  (RingHom.toOpposite (algebraMap (A ⧸ I) (Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 r A I)))
      (fun a b => Algebra.commute_algebraMap_left a _)).comp (padicToQuot A I hpI)

def theta (hpI : (p : A) ∈ I) :
    ℤ_[p] ⊗[ℤ] (CuspForm.heckeRingH M H 2)ᵐᵒᵖ →ₐ[ℤ] (Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 r A I))ᵐᵒᵖ :=
  Algebra.TensorProduct.lift (padicToEndOp M H r A I hpI).toIntAlgHom
    (RingHom.op (rhoR M H r A I)).toIntAlgHom
    (fun c y => (Algebra.commute_algebraMap_left (padicToQuot A I hpI c)
      (rhoR M H r A I (MulOpposite.unop y))).op)

theorem theta_one_tmul (hpI : (p : A) ∈ I) (t : CuspForm.heckeRingH M H 2) :
    theta M H r A I hpI ((1 : ℤ_[p]) ⊗ₜ MulOpposite.op t) = MulOpposite.op (CuspForm.twoCuspEndMod I t) := by
  rw [theta, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end FormsSide

section Assembly

open CohCarrier ModularCurve

theorem mainThm (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (ops : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      ops g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range ops) = ⊤)
    (r : ℕ) (A : Subring ℂ) (I : Ideal A) (hpI : (p : A) ∈ I) :
    ∃ τ : 𝕋 →+* Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 r A I),
      ∀ g : CohCarrier.Gen M S, τ (ops g) = CuspForm.twoCuspGenMod I S g := by
  classical

  obtain ⟨e, he⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf M p H S hin

  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH M H) (isCongruenceSubgroup_gammaH M H)
  haveI : Module.Free ℤ ↥(Lat M H) := Module.Free.of_basis b
  haveI : Module.Finite ℤ ↥(Lat M H) := Module.Finite.of_basis b

  have hιZ : ∀ z : ℤ, iotaR M H (algebraMap ℤ _ z) = algebraMap ℤ (Module.End ℤ ↥(Lat M H)) z := fun z =>
    DFunLike.congr_fun (RingHom.ext_int ((iotaR M H).comp (algebraMap ℤ (CuspForm.heckeRingH M H 2)ᵐᵒᵖ))
      (algebraMap ℤ (Module.End ℤ ↥(Lat M H)))) z
  let ιA : (CuspForm.heckeRingH M H 2)ᵐᵒᵖ →ₐ[ℤ] Module.End ℤ ↥(Lat M H) :=
    { iotaR M H with commutes' := hιZ }
  have hιA : Function.Injective ιA := fun T T' h => iotaR_injective M H h
  obtain ⟨τ', hτ'⟩ := exists_ringHom_of_tensor (R := ℤ) ℤ_[p] e ops hgen ιA hιA
    (fun g => MulOpposite.op (genR M H S g))
    (fun g x => by rw [hop]; exact key M H S e he g x) (theta M H r A I hpI).toRingHom

  refine ⟨RingHom.unop (τ'.comp (RingHom.fromOpposite (RingHom.id 𝕋) fun x y => Commute.all x y)), fun g => ?_⟩
  show MulOpposite.unop (τ' (ops g)) = _
  rw [hτ', AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, theta_one_tmul]
  rfl

end Assembly

end HeckeCompatRed
p2m_reactivate "P2MW.S_ModularCurve_exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod.HeckeCompatRed"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod.HeckeCompatRed"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (r : ℕ) (A : Subring ℂ) (I : Ideal A) (hpI : (p : A) ∈ I) :
    ∃ τ : 𝕋 →+* Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 r A I),
      ∀ g : CohCarrier.Gen M S, τ (op g) = CuspForm.twoCuspGenMod I S g :=
  HeckeCompatRed.mainThm p M H S hin op hop hgen r A I hpI

end S_ModularCurve_exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_moduleEnd_twoCuspForms_apply_eq_twoCuspGenMod (solution)
