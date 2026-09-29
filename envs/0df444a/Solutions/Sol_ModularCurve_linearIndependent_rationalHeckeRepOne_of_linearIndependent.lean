-- Prove2me | solution 1 for ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bf5ac947-403d-5f86-93d1-9fa3b5a0c275

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_CuspForm_heckeULinH_comm
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable
import Theorems.Thm_ModularCurve_pic0Congr_jOne_jH_bot_compat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open scoped TensorProduct

namespace FC3B
namespace Abstract

open ModularCurve

section Functorial

variable {p : ℕ} [Fact p.Prime] {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M']
  [AddCommGroup M'']

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

theorem tateMap_surjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) :
    Function.Surjective (tateMap p f) := by
  intro y
  have hfin : ∀ n, IsOfFinAddOrder ((y : ℕ → M') n) := fun n => by
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    exact TateModule.torsion y n
  choose x hx using fun n => (AddMonoidHom.mem_range).1 (hsurj _ (hfin n))
  refine ⟨⟨x, fun n => ⟨hf ?_, hf ?_⟩⟩, Subtype.ext (funext fun n => hx n)⟩
  · rw [map_zsmul, hx, map_zero, TateModule.torsion]
  · rw [map_zsmul, hx, hx, TateModule.compat]

def tateEquivOfInjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) :
    TateModule p M ≃ₗ[ℤ_[p]] TateModule p M' :=
  LinearEquiv.ofBijective (tateMap p f) ⟨tateMap_injective f hf, tateMap_surjective f hf hsurj⟩

@[scoped simp] theorem tateEquivOfInjective_apply (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) (x : TateModule p M) :
    tateEquivOfInjective f hf hsurj x = tateMap p f x := rfl

theorem tateMap_naturality (u : M →+ M') (S : M →+ M) (T : M' →+ M')
    (h : ∀ m, u (S m) = T (u m)) (x : TateModule p M) :
    tateMap p u (tateMap p S x) = tateMap p T (tateMap p u x) :=
  Subtype.ext (funext fun n => h _)

end Functorial

section Torus

open Module

variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V]
variable (K) (p : ℕ) [Fact p.Prime] (Λ : Submodule ℤ V)

theorem natCast_ne_zero_K : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

def divLevel (n : ℕ) : V →+ V ⧸ Λ where
  toFun v := Submodule.Quotient.mk ((((p : K) ^ n)⁻¹) • v)
  map_zero' := by rw [smul_zero, Submodule.Quotient.mk_zero]
  map_add' v w := by rw [smul_add, Submodule.Quotient.mk_add]

theorem divLevel_apply (n : ℕ) (v : V) :
    divLevel K p Λ n v = Submodule.Quotient.mk ((((p : K) ^ n)⁻¹) • v) := rfl

theorem natCast_pow_zsmul_eq (n : ℕ) (v : V) : (((p ^ n : ℕ) : ℤ) • v) = ((p : K) ^ n) • v := by
  rw [Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul K, Nat.cast_pow]

theorem natCast_zsmul_eq (v : V) : (((p : ℕ) : ℤ) • v) = (p : K) • v := by
  rw [Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul K]

@[scoped simp] theorem divLevel_natCast_pow_smul (n : ℕ) (v : V) :
    divLevel K p Λ n (((p ^ n : ℕ) : ℤ) • v) = Submodule.Quotient.mk v := by
  rw [divLevel_apply, natCast_pow_zsmul_eq K p, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero n (natCast_ne_zero_K K p)), one_smul]

theorem divLevel_succ_natCast_smul (n : ℕ) (v : V) :
    divLevel K p Λ (n + 1) (((p : ℕ) : ℤ) • v) = divLevel K p Λ n v := by
  rw [divLevel_apply, divLevel_apply, natCast_zsmul_eq K p, smul_smul, pow_succ, mul_inv,
    inv_mul_cancel_right₀ (natCast_ne_zero_K K p)]

theorem divLevel_zero (v : V) : divLevel K p Λ 0 v = Submodule.Quotient.mk v := by
  rw [divLevel_apply, pow_zero, inv_one, one_smul]

theorem divLevel_coe_eq_of_eq_add (n : ℕ) (l₁ l₂ μ : Λ) (h : l₁ = l₂ + ((p ^ n : ℕ) : ℤ) • μ) :
    divLevel K p Λ n (l₁ : V) = divLevel K p Λ n (l₂ : V) := by
  rw [h, Submodule.coe_add, Submodule.coe_smul, map_add, divLevel_natCast_pow_smul,
    (Submodule.Quotient.mk_eq_zero Λ).2 μ.2, add_zero]

def iota : Λ →ₗ[ℤ] TateModule p (V ⧸ Λ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun l => ⟨fun n => divLevel K p Λ n (l : V), fun n =>
        ⟨by rw [← map_zsmul, divLevel_natCast_pow_smul, (Submodule.Quotient.mk_eq_zero Λ).2 l.2],
         by rw [← map_zsmul, divLevel_succ_natCast_smul]⟩⟩
      map_zero' := Subtype.ext (funext fun n => by
        show divLevel K p Λ n ((0 : Λ) : V) = ((0 : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n
        rw [Submodule.coe_zero, map_zero, TateModule.coe_zero, Pi.zero_apply])
      map_add' := fun l m => Subtype.ext (funext fun n => by
        show divLevel K p Λ n ((l + m : Λ) : V) = divLevel K p Λ n (l : V) + divLevel K p Λ n (m : V)
        rw [Submodule.coe_add, map_add]) }

@[scoped simp] theorem coe_iota_apply (l : Λ) (n : ℕ) :
    ((iota K p Λ l : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n = divLevel K p Λ n (l : V) := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Λ)

def psi : (ι → ℤ_[p]) →ₗ[ℤ_[p]] TateModule p (V ⧸ Λ) :=
  ∑ i, (LinearMap.proj i : (ι → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]).smulRight (iota K p Λ (b i))

theorem psi_apply (c : ι → ℤ_[p]) : psi K p Λ b c = ∑ i, c i • iota K p Λ (b i) := by
  simp only [psi, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

def lam (c : ι → ℤ_[p]) (n : ℕ) : Λ := ∑ i, (((c i).appr n : ℕ) : ℤ) • b i

theorem coe_psi_apply (c : ι → ℤ_[p]) (n : ℕ) :
    ((psi K p Λ b c : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n = divLevel K p Λ n (lam p Λ b c n : V) := by
  rw [psi_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, lam, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TateModule.smul_apply, coe_iota_apply, ← map_zsmul, Submodule.coe_smul]

theorem equivFun_lam (c : ι → ℤ_[p]) (n : ℕ) (i : ι) :
    b.equivFun (lam p Λ b c n) i = (((c i).appr n : ℕ) : ℤ) := by
  have : lam p Λ b c n = b.equivFun.symm fun i => (((c i).appr n : ℕ) : ℤ) := by
    rw [Basis.equivFun_symm_apply]; rfl
  rw [this, LinearEquiv.apply_symm_apply]

theorem exists_eq_smul_of_divLevel_eq_zero (n : ℕ) (l : Λ)
    (h : divLevel K p Λ n (l : V) = 0) : ∃ μ : Λ, l = ((p ^ n : ℕ) : ℤ) • μ := by
  rw [divLevel_apply, Submodule.Quotient.mk_eq_zero] at h
  refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, natCast_pow_zsmul_eq K p, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero n (natCast_ne_zero_K K p)), one_smul]

theorem psi_injective : Function.Injective (psi K p Λ b) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  refine (PadicInt.ext_of_toZModPow).1 fun n => ?_
  rw [Pi.zero_apply, map_zero, TateModule.toZModPow_eq_appr]
  have hn : ((psi K p Λ b c : TateModule p (V ⧸ Λ)) : ℕ → V ⧸ Λ) n = 0 := by
    rw [hc, TateModule.coe_zero, Pi.zero_apply]
  rw [coe_psi_apply] at hn
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_divLevel_eq_zero K p Λ n _ hn
  have hi := equivFun_lam p Λ b c n i
  rw [hμ, map_zsmul, Pi.smul_apply, smul_eq_mul] at hi
  have : (((((c i).appr n : ℕ) : ℤ)) : ZMod (p ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨_, hi.symm⟩
  rwa [Int.cast_natCast] at this

theorem psi_surjective : Function.Surjective (psi K p Λ b) := by
  intro x
  have hp : p.Prime := Fact.out

  choose v hv using fun n => Submodule.Quotient.mk_surjective Λ ((x : ℕ → V ⧸ Λ) n)

  have hΛ : ∀ n, (((p ^ n : ℕ) : ℤ) • v n) ∈ Λ := fun n => by
    rw [← Submodule.Quotient.mk_eq_zero]
    change Submodule.mkQ Λ (((p ^ n : ℕ) : ℤ) • v n) = 0
    rw [map_zsmul, Submodule.mkQ_apply, hv]
    exact TateModule.torsion x n

  have hδ : ∀ n, (((p : ℕ) : ℤ) • v (n + 1) - v n) ∈ Λ := fun n => by
    rw [← Submodule.Quotient.eq]
    change Submodule.mkQ Λ (((p : ℕ) : ℤ) • v (n + 1)) = Submodule.Quotient.mk (v n)
    rw [map_zsmul, Submodule.mkQ_apply, hv, hv]
    exact TateModule.compat x n
  set L : ℕ → Λ := fun n => ⟨_, hΛ n⟩ with hL
  set δ : ℕ → Λ := fun n => ⟨_, hδ n⟩ with hδdef
  have hLsucc : ∀ n, L (n + 1) = L n + ((p ^ n : ℕ) : ℤ) • δ n := fun n => by
    refine Subtype.ext ?_
    simp only [hL, hδdef, Submodule.coe_add, Submodule.coe_smul, smul_sub, smul_smul]
    push_cast
    rw [pow_succ, add_sub_cancel]
  set a : ℕ → ι → ℤ := fun n => b.equivFun (L n) with ha
  have hdvd : ∀ i n, (p : ℤ) ^ n ∣ a (n + 1) i - a n i := fun i n => by
    refine ⟨b.equivFun (δ n) i, ?_⟩
    rw [ha]
    dsimp only
    rw [hLsucc, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      Nat.cast_pow]
  let c : ι → ℤ_[p] := fun i =>
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => a n i) p (hdvd i))
  have hc : ∀ i n, PadicInt.toZModPow n (c i) = (a n i : ZMod (p ^ n)) := fun i n =>
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => a n i) p (hdvd i) n
  refine ⟨c, Subtype.ext (funext fun n => ?_)⟩
  rw [coe_psi_apply, ← hv, ← divLevel_natCast_pow_smul K p Λ n (v n)]
  change divLevel K p Λ n (lam p Λ b c n : V) = divLevel K p Λ n (L n : V)

  have hcoef : ∀ i, ∃ e : ℤ, (((c i).appr n : ℕ) : ℤ) - a n i = ((p ^ n : ℕ) : ℤ) * e := fun i => by
    have h1 : ((a n i : ℤ) : ZMod (p ^ n)) = ((((c i).appr n : ℕ) : ℤ) : ZMod (p ^ n)) := by
      rw [Int.cast_natCast, ← TateModule.toZModPow_eq_appr, hc]
    obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    exact ⟨e, he⟩
  choose e he using hcoef
  refine divLevel_coe_eq_of_eq_add K p Λ n _ _ (∑ i, e i • b i) ?_
  apply b.equivFun.injective
  funext i
  rw [equivFun_lam, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ← sub_eq_iff_eq_add', he]
  congr 1
  have : (∑ j, e j • b j) = b.equivFun.symm e := (Basis.equivFun_symm_apply b e).symm
  rw [this, LinearEquiv.apply_symm_apply]

def psiEquiv : (ι → ℤ_[p]) ≃ₗ[ℤ_[p]] TateModule p (V ⧸ Λ) :=
  LinearEquiv.ofBijective (psi K p Λ b) ⟨psi_injective K p Λ b, psi_surjective K p Λ b⟩

def phi2 : ℤ_[p] ⊗[ℤ] Λ ≃ₗ[ℤ_[p]] TateModule p (V ⧸ Λ) :=
  (Algebra.TensorProduct.basis ℤ_[p] b).equivFun.trans (psiEquiv K p Λ b)

theorem phi2_toLinearMap_eq :
    (phi2 K p Λ b).toLinearMap = (iota K p Λ).liftBaseChange ℤ_[p] := by
  refine (Algebra.TensorProduct.basis ℤ_[p] b).ext fun i => ?_
  rw [LinearEquiv.coe_coe, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul,
    ← Algebra.TensorProduct.basis_apply, phi2, LinearEquiv.trans_apply, psiEquiv,
    LinearEquiv.ofBijective_apply, psi_apply]
  rw [Finset.sum_eq_single i]
  · rw [Basis.equivFun_self, if_pos rfl, one_smul]
  · intro j _ hji
    rw [Basis.equivFun_self, if_neg (Ne.symm hji), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

@[scoped simp] theorem phi2_tmul (a : ℤ_[p]) (l : Λ) : phi2 K p Λ b (a ⊗ₜ l) = a • iota K p Λ l := by
  rw [← LinearEquiv.coe_coe, phi2_toLinearMap_eq, LinearMap.liftBaseChange_tmul]

variable (T : V →ₗ[K] V) (hT : ∀ v ∈ Λ, T v ∈ Λ)

def quotEnd : V ⧸ Λ →+ V ⧸ Λ :=
  (Λ.mapQ Λ T.toAddMonoidHom.toIntLinearMap fun v hv => hT v hv).toAddMonoidHom

@[scoped simp] theorem quotEnd_mk (v : V) :
    quotEnd K Λ T hT (Submodule.Quotient.mk v) = Submodule.Quotient.mk (T v) := rfl

theorem quotEnd_divLevel (n : ℕ) (v : V) :
    quotEnd K Λ T hT (divLevel K p Λ n v) = divLevel K p Λ n (T v) := by
  rw [divLevel_apply, divLevel_apply, quotEnd_mk, LinearMap.map_smul]

variable (TΛ : Λ →ₗ[ℤ] Λ)

theorem iota_restrict (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (l : Λ) :
    iota K p Λ (TΛ l) = tateMap p (quotEnd K Λ T hT) (iota K p Λ l) :=
  Subtype.ext (funext fun n => by
    rw [coe_iota_apply, coe_tateMap_apply, coe_iota_apply, hTΛ, quotEnd_divLevel])

theorem phi2_baseChange (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (z : ℤ_[p] ⊗[ℤ] Λ) :
    phi2 K p Λ b (TΛ.baseChange ℤ_[p] z) = tateMap p (quotEnd K Λ T hT) (phi2 K p Λ b z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a l =>
      rw [LinearMap.baseChange_tmul, phi2_tmul, phi2_tmul, iota_restrict K p Λ T hT TΛ hTΛ, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem assemble (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l)
    {M : Type} [AddCommGroup M] (u : M →+ V ⧸ Λ) (hu : Function.Injective u)
    (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range) (S : M →+ M)
    (hS : ∀ m, u (S m) = quotEnd K Λ T hT (u m)) (x y : TateModule p M)
    (hy : ∀ n, (y : ℕ → M) n = S ((x : ℕ → M) n)) :
    ((tateEquivOfInjective u hu htors).trans (phi2 K p Λ b).symm) y =
      TΛ.baseChange ℤ_[p] (((tateEquivOfInjective u hu htors).trans (phi2 K p Λ b).symm) x) := by
  have hy' : y = tateMap p S x := Subtype.ext (funext hy)
  subst hy'
  apply (phi2 K p Λ b).injective
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
    phi2_baseChange K p Λ b T hT TΛ hTΛ, LinearEquiv.apply_symm_apply,
    tateEquivOfInjective_apply, tateEquivOfInjective_apply]
  exact tateMap_naturality u S _ hS x

end Torus

section LinAlg

theorem linearIndependent_of_ker_le {R M M₁ M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M →ₗ[R] M₁) (g : M →ₗ[R] M₂) (hker : ∀ m, f m = 0 → g m = 0)
    {ι : Type*} (v : ι → M) (h : LinearIndependent R (fun i => g (v i))) :
    LinearIndependent R (fun i => f (v i)) := by
  rw [linearIndependent_iff] at h ⊢
  intro l hl
  apply h l
  have h1 : Finsupp.linearCombination R (fun i => f (v i)) l = f (Finsupp.linearCombination R v l) :=
    (Finsupp.apply_linearCombination R f v l).symm
  have h2 : Finsupp.linearCombination R (fun i => g (v i)) l = g (Finsupp.linearCombination R v l) :=
    (Finsupp.apply_linearCombination R g v l).symm
  rw [h2]
  exact hker _ (h1 ▸ hl)

variable {n : ℕ}

def flat (K : Type) [CommRing K] : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K) where
  toFun A := fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_flat (K : Type) [CommRing K] : LinearMap.ker (flat (n := n) K) = ⊥ := by
  refine LinearMap.ker_eq_bot.mpr ?_
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem linearIndependent_padic_of_int (p : ℕ) [Fact p.Prime] {ι : Type*}
    (v : ι → Matrix (Fin n) (Fin n) ℤ) (hv : LinearIndependent ℤ v) :
    LinearIndependent ℚ_[p] (fun i => (v i).map (Int.cast : ℤ → ℚ_[p])) := by
  have h1 : LinearIndependent ℤ (fun i => flat ℤ (v i)) := hv.map' (flat ℤ) (ker_flat ℤ)
  have h2 : LinearIndependent ℚ_[p] (fun i => (algebraMap ℤ ℚ_[p]) ∘ (flat ℤ (v i))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ_[p])).mpr h1
  have h3 : (fun i => (algebraMap ℤ ℚ_[p]) ∘ (flat ℤ (v i))) =
      fun i => flat ℚ_[p] ((v i).map (Int.cast : ℤ → ℚ_[p])) := by
    funext i; funext ij; simp [flat]
  rw [h3] at h2
  exact LinearIndependent.of_comp (flat ℚ_[p]) h2

end LinAlg

section Tate

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]
variable {Λ : Type} [AddCommGroup Λ] (ρΛ : HeckeAlgOne →+* Module.End ℤ Λ)
variable {n : ℕ} (bΛ : Module.Basis (Fin n) ℤ Λ)

def M : HeckeAlgOne →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv bΛ).toRingEquiv.toRingHom.comp ρΛ

theorem M_apply (t : HeckeAlgOne) : M ρΛ bΛ t = LinearMap.toMatrix bΛ bΛ (ρΛ t) := rfl

def Mp : HeckeAlgOne →+* Matrix (Fin n) (Fin n) ℚ_[p] :=
  ((Int.castRingHom ℚ_[p]).mapMatrix).comp (M ρΛ bΛ)

theorem Mp_apply (t : HeckeAlgOne) : Mp p ρΛ bΛ t = (M ρΛ bΛ t).map (Int.cast : ℤ → ℚ_[p]) := rfl

variable (e₁ : TateModule p J ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ)

def E1 : RationalTateModule p J ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ) :=
  e₁.baseChange ℤ_[p] ℚ_[p] _ _

def E2 : ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ) ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ] Λ :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[p] ℚ_[p] ℚ_[p] Λ

def E3 : ℚ_[p] ⊗[ℤ] Λ ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (Algebra.TensorProduct.basis ℚ_[p] bΛ).equivFun

def E : RationalTateModule p J ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (E1 p J e₁).trans ((E2 p).trans (E3 p bΛ))

theorem E1_equivariant (t : HeckeAlgOne)
    (he : ∀ t x, e₁ (tateHeckeRepOne p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    (v : RationalTateModule p J) :
    E1 p J e₁ (rationalHeckeRepOne p J t v) =
      ((ρΛ t).baseChange ℤ_[p]).baseChange ℚ_[p] (E1 p J e₁ v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp [E1, rationalHeckeRepOne_tmul, LinearEquiv.baseChange, he]
  | add x y hx hy => simp [map_add, hx, hy]

theorem E2_equivariant (t : HeckeAlgOne) (v : ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ)) :
    E2 p (((ρΛ t).baseChange ℤ_[p]).baseChange ℚ_[p] v) = (ρΛ t).baseChange ℚ_[p] (E2 p v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => simp [E2]
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add]
  | add x y hx hy => simp [map_add, hx, hy]

theorem E3_equivariant (t : HeckeAlgOne) (v : ℚ_[p] ⊗[ℤ] Λ) :
    E3 p bΛ ((ρΛ t).baseChange ℚ_[p] v) = (Mp p ρΛ bΛ t).mulVec (E3 p bΛ v) := by
  have h := LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis ℚ_[p] bΛ)
    (Algebra.TensorProduct.basis ℚ_[p] bΛ) ((ρΛ t).baseChange ℚ_[p]) v
  rw [LinearMap.toMatrix_baseChange] at h
  simp only [E3, Module.Basis.equivFun_apply]
  rw [← h]
  congr 1

theorem E_equivariant
    (he : ∀ t x, e₁ (tateHeckeRepOne p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    (t : HeckeAlgOne) (v : RationalTateModule p J) :
    E p J bΛ e₁ (rationalHeckeRepOne p J t v) = (Mp p ρΛ bΛ t).mulVec (E p J bΛ e₁ v) := by
  simp only [E, LinearEquiv.trans_apply]
  rw [E1_equivariant p J ρΛ e₁ t he, E2_equivariant, E3_equivariant]

def Δ : Module.End ℚ_[p] (RationalTateModule p J) →ₗ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p] :=
  (LinearMap.toMatrix' : ((Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])) ≃ₗ[ℚ_[p]] _).toLinearMap ∘ₗ
    ((E p J bΛ e₁).conj : Module.End ℚ_[p] (RationalTateModule p J) ≃ₗ[ℚ_[p]] _).toLinearMap

omit [Module HeckeAlgOne J] in
theorem Δ_apply (f : Module.End ℚ_[p] (RationalTateModule p J)) :
    Δ p J bΛ e₁ f =
      LinearMap.toMatrix' (((E p J bΛ e₁).toLinearMap ∘ₗ f) ∘ₗ (E p J bΛ e₁).symm.toLinearMap) := by
  simp only [Δ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.conj_apply]

theorem Δ_rationalHeckeRepOne
    (he : ∀ t x, e₁ (tateHeckeRepOne p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x)) (t : HeckeAlgOne) :
    Δ p J bΛ e₁ (rationalHeckeRepOne p J t) = Mp p ρΛ bΛ t := by
  have hconj : ((E p J bΛ e₁).toLinearMap ∘ₗ rationalHeckeRepOne p J t) ∘ₗ (E p J bΛ e₁).symm.toLinearMap
      = Matrix.toLin' (Mp p ρΛ bΛ t) := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Matrix.toLin'_apply]
    rw [E_equivariant p J ρΛ bΛ e₁ he, LinearEquiv.apply_symm_apply]
  rw [Δ_apply, hconj, LinearMap.toMatrix'_toLin']

theorem linearIndependent_rationalHeckeRepOne_of_matrix
    (he : ∀ t x, e₁ (tateHeckeRepOne p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    {ι : Type*} (t : ι → HeckeAlgOne)
    (h : LinearIndependent ℚ_[p] (fun i => Mp p ρΛ bΛ (t i))) :
    LinearIndependent ℚ_[p] (fun i => rationalHeckeRepOne p J (t i)) := by
  have h' : LinearIndependent ℚ_[p] (fun i => Δ p J bΛ e₁ (rationalHeckeRepOne p J (t i))) := by
    have hfun : (fun i => Δ p J bΛ e₁ (rationalHeckeRepOne p J (t i))) = fun i => Mp p ρΛ bΛ (t i) := by
      funext i; exact Δ_rationalHeckeRepOne p J ρΛ bΛ e₁ he (t i)
    rw [hfun]; exact h
  exact LinearIndependent.of_comp (Δ p J bΛ e₁) h'

end Tate

section Restrict

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D]
variable (Λ : Submodule ℤ D) (ρD : HeckeAlgOne →+* Module.End K D)
  (hst : ∀ (t : HeckeAlgOne), ∀ v ∈ Λ, ρD t v ∈ Λ)

def resΛ (t : HeckeAlgOne) : Λ →ₗ[ℤ] Λ :=
  ((ρD t).restrictScalars ℤ).restrict (p := Λ) (q := Λ) (fun v hv => hst t v hv)

@[scoped simp] theorem coe_resΛ_apply (t : HeckeAlgOne) (l : Λ) : ((resΛ Λ ρD hst t l : Λ) : D) = ρD t l := rfl

def rhoΛ : HeckeAlgOne →+* Module.End ℤ Λ where
  toFun := resΛ Λ ρD hst
  map_one' := by
    refine LinearMap.ext fun l => Subtype.ext ?_
    rw [coe_resΛ_apply, map_one]; rfl
  map_mul' s t := by
    refine LinearMap.ext fun l => Subtype.ext ?_
    rw [coe_resΛ_apply, map_mul]; rfl
  map_zero' := by
    refine LinearMap.ext fun l => Subtype.ext ?_
    rw [coe_resΛ_apply, map_zero]; rfl
  map_add' s t := by
    refine LinearMap.ext fun l => Subtype.ext ?_
    rw [coe_resΛ_apply, map_add]; rfl

@[scoped simp] theorem coe_rhoΛ_apply (t : HeckeAlgOne) (l : Λ) : ((rhoΛ Λ ρD hst t l : Λ) : D) = ρD t l := rfl

end Restrict

section Annih

variable {K : Type} [Field K] [CharZero K] {D : Type} [AddCommGroup D] [Module K D]
variable (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]
variable (Λ : Submodule ℤ D) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
  (ρD : HeckeAlgOne →+* Module.End K D)
  (hst : ∀ (t : HeckeAlgOne), ∀ v ∈ Λ, ρD t v ∈ Λ)
  (hspan : ∀ (t : HeckeAlgOne), (∀ i, ρD t ((b i : Λ) : D) = 0) → ρD t = 0)
  (u : J →+ D ⧸ Λ) (hinj : Function.Injective u)
  (hu : ∀ (t : HeckeAlgOne) (x : J) (φ : D), u x = Submodule.Quotient.mk φ → u (t • x) = Submodule.Quotient.mk (ρD t φ))

include hspan hinj hu in

theorem smul_eq_zero_of_rhoΛ_eq_zero (s : HeckeAlgOne) (hs : rhoΛ Λ ρD hst s = 0) (x : J) : s • x = 0 := by
  have hD : ρD s = 0 := by
    refine hspan s fun i => ?_
    rw [← coe_rhoΛ_apply Λ ρD hst s (b i), hs, LinearMap.zero_apply, Submodule.coe_zero]
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective Λ (u x)
  have h1 : u (s • x) = 0 := by
    rw [hu s x φ hφ.symm, hD, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  exact hinj (h1.trans u.map_zero.symm)

include hspan hinj hu in

theorem linearIndependent_M_of {ι : Type} (t : ι → HeckeAlgOne)
    (hli : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) (t i))) :
    LinearIndependent ℤ (fun i => M (rhoΛ Λ ρD hst) b (t i)) := by
  let f : HeckeAlgOne →ₗ[ℤ] Matrix (Fin n) (Fin n) ℤ := (M (rhoΛ Λ ρD hst) b).toAddMonoidHom.toIntLinearMap
  let g : HeckeAlgOne →ₗ[ℤ] (HeckeAlgOne ⧸ Module.annihilator HeckeAlgOne J) :=
    (Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J)).toAddMonoidHom.toIntLinearMap
  have hker : ∀ s, f s = 0 → g s = 0 := by
    intro s hs
    have hs' : rhoΛ Λ ρD hst s = 0 := (LinearMap.toMatrix b b).map_eq_zero_iff.mp hs
    show Ideal.Quotient.mk (Module.annihilator HeckeAlgOne J) s = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
    intro x
    exact smul_eq_zero_of_rhoΛ_eq_zero J Λ b ρD hst hspan u hinj hu s hs' x
  have hli' : LinearIndependent ℤ (fun i => g (t i)) := by
    first | exact hli | (convert hli using 1; funext i; rfl)
  exact linearIndependent_of_ker_le f g hker t hli'

end Annih

section BettiTate

variable (K : Type) [Field K] [CharZero K] {D : Type} [AddCommGroup D] [Module K D]
variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]
variable (Λ : Submodule ℤ D) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
  (ρD : HeckeAlgOne →+* Module.End K D)
  (hst : ∀ (t : HeckeAlgOne), ∀ v ∈ Λ, ρD t v ∈ Λ)
  (u : J →+ D ⧸ Λ) (hinj : Function.Injective u)
  (htors : ∀ y : D ⧸ Λ, IsOfFinAddOrder y → y ∈ u.range)
  (hu : ∀ (t : HeckeAlgOne) (x : J) (φ : D), u x = Submodule.Quotient.mk φ → u (t • x) = Submodule.Quotient.mk (ρD t φ))

def e₁ : TateModule p J ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ := by
  classical
  exact (tateEquivOfInjective u hinj htors).trans (phi2 K p Λ b).symm

include hu in
theorem e₁_equivariant (t : HeckeAlgOne) (x : TateModule p J) :
    e₁ K p J Λ b u hinj htors (tateHeckeRepOne p J t x) = (rhoΛ Λ ρD hst t).baseChange ℤ_[p] (e₁ K p J Λ b u hinj htors x) := by
  classical
  have hS : ∀ m : J, u ((DistribSMul.toAddMonoidHom J t) m) = quotEnd K Λ (ρD t) (hst t) (u m) := fun m => by
    obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective Λ (u m)
    rw [DistribSMul.toAddMonoidHom_apply, hu t m φ hφ.symm, ← quotEnd_mk K Λ (ρD t) (hst t) φ, hφ]
  exact assemble K p Λ b (ρD t) (hst t) (rhoΛ Λ ρD hst t) (fun l => rfl) u hinj htors
    (DistribSMul.toAddMonoidHom J t) hS x (tateHeckeRepOne p J t x) (fun n => rfl)

end BettiTate

theorem linearIndependent_rationalHeckeRepOne_of_uniformization
    (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    {K : Type} [Field K] [CharZero K] {D : Type} [AddCommGroup D] [Module K D]
    (Λ : Submodule ℤ D) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (ρD : ModularCurve.HeckeAlgOne →+* Module.End K D)
    (hst : ∀ (t : ModularCurve.HeckeAlgOne), ∀ v ∈ Λ, ρD t v ∈ Λ)
    (hspan : ∀ (t : ModularCurve.HeckeAlgOne), (∀ i, ρD t ((b i : Λ) : D) = 0) → ρD t = 0)
    (u : J →+ D ⧸ Λ) (hinj : Function.Injective u)
    (htors : ∀ y : D ⧸ Λ, IsOfFinAddOrder y → y ∈ u.range)
    (hu : ∀ (t : ModularCurve.HeckeAlgOne) (x : J) (φ : D),
      u x = Submodule.Quotient.mk φ → u (t • x) = Submodule.Quotient.mk (ρD t φ))
    {ι : Type} (t : ι → ModularCurve.HeckeAlgOne)
    (hli : LinearIndependent ℤ (fun i =>
      Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlgOne J) (t i))) :
    LinearIndependent ℚ_[p] (fun i => ModularCurve.rationalHeckeRepOne p J (t i)) := by

  have hM : LinearIndependent ℤ (fun i => M (rhoΛ Λ ρD hst) b (t i)) :=
    linearIndependent_M_of J Λ b ρD hst hspan u hinj hu t hli

  have hMp : LinearIndependent ℚ_[p] (fun i => Mp p (rhoΛ Λ ρD hst) b (t i)) :=
    linearIndependent_padic_of_int p _ hM

  exact linearIndependent_rationalHeckeRepOne_of_matrix p J (rhoΛ Λ ρD hst) b (e₁ K p J Λ b u hinj htors)
    (e₁_equivariant K p J Λ b ρD hst u hinj htors hu) t hMp

end Abstract
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract"
end FC3B
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B"

namespace FC3B
namespace Inst

open ModularCurve
open scoped MatrixGroups

variable (M : ℕ) [NeZero M]

abbrev Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH M ⊥
abbrev D : Type := Module.Dual ℂ (CuspForm (Γ M) 2)
abbrev Λ : Submodule ℤ (D M) := periodLatticeOf (Γ M)

noncomputable def opF : Nat.Primes ⊕ ℕ → Module.End ℂ (CuspForm (Γ M) 2)
  | Sum.inl ℓ =>
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      if h : (ℓ : ℕ) ∣ M then CuspForm.heckeULinH (M := M) (H := ⊥) 2 (ℓ : ℕ)
      else CuspForm.heckeTLinH (M := M) (H := ⊥) 2 ℓ.2 h
  | Sum.inr d => if h : Nat.Coprime d M then CuspForm.diamondLinH (M := M) (H := ⊥) 2 (ZMod.unitOfCoprime d h) else 1

theorem opF_inl_of_dvd (ℓ : Nat.Primes) (h : (ℓ : ℕ) ∣ M) :
    opF M (Sum.inl ℓ) = (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; CuspForm.heckeULinH (M := M) (H := ⊥) 2 (ℓ : ℕ)) := by
  simp only [opF, dif_pos h]

theorem opF_inl_of_not_dvd (ℓ : Nat.Primes) (h : ¬ (ℓ : ℕ) ∣ M) :
    opF M (Sum.inl ℓ) = (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; CuspForm.heckeTLinH (M := M) (H := ⊥) 2 ℓ.2 h) := by
  simp only [opF, dif_neg h]

theorem opF_inr_of_isUnit (d : ℕ) (h : Nat.Coprime d M) :
    opF M (Sum.inr d) = CuspForm.diamondLinH (M := M) (H := ⊥) 2 (ZMod.unitOfCoprime d h) := by
  simp only [opF, dif_pos h]

theorem opF_inr_of_not_isUnit (d : ℕ) (h : ¬ Nat.Coprime d M) : opF M (Sum.inr d) = 1 := by
  simp only [opF, dif_neg h]

theorem opF_comm (i j : Nat.Primes ⊕ ℕ) : opF M i * opF M j = opF M j * opF M i := by
  obtain ⟨hTT, hTU, hTD, hUD, hDD⟩ := CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M ⊥ 2
  apply LinearMap.ext; intro f
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rcases i with ℓ | d <;> rcases j with ℓ' | d'
  · haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; haveI : NeZero (ℓ' : ℕ) := ⟨ℓ'.2.ne_zero⟩
    by_cases h : (ℓ : ℕ) ∣ M <;> by_cases h' : (ℓ' : ℕ) ∣ M
    · rw [opF_inl_of_dvd M ℓ h, opF_inl_of_dvd M ℓ' h']; exact CuspForm.heckeULinH_comm M ⊥ 2 ℓ.2 h ℓ'.2 h' f
    · rw [opF_inl_of_dvd M ℓ h, opF_inl_of_not_dvd M ℓ' h']; exact (hTU _ ℓ'.2 h' _ ℓ.2 h f).symm
    · rw [opF_inl_of_not_dvd M ℓ h, opF_inl_of_dvd M ℓ' h']; exact hTU _ ℓ.2 h _ ℓ'.2 h' f
    · rw [opF_inl_of_not_dvd M ℓ h, opF_inl_of_not_dvd M ℓ' h']; exact hTT _ _ ℓ.2 h ℓ'.2 h' f
  · haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    by_cases h' : Nat.Coprime d' M
    · rw [opF_inr_of_isUnit M d' h']
      by_cases h : (ℓ : ℕ) ∣ M
      · rw [opF_inl_of_dvd M ℓ h]; exact hUD _ ℓ.2 h _ f
      · rw [opF_inl_of_not_dvd M ℓ h]; exact hTD _ ℓ.2 h _ f
    · rw [opF_inr_of_not_isUnit M d' h']; rfl
  · haveI : NeZero (ℓ' : ℕ) := ⟨ℓ'.2.ne_zero⟩
    by_cases h : Nat.Coprime d M
    · rw [opF_inr_of_isUnit M d h]
      by_cases h' : (ℓ' : ℕ) ∣ M
      · rw [opF_inl_of_dvd M ℓ' h']; exact (hUD _ ℓ'.2 h' _ f).symm
      · rw [opF_inl_of_not_dvd M ℓ' h']; exact (hTD _ ℓ'.2 h' _ f).symm
    · rw [opF_inr_of_not_isUnit M d h]; rfl
  · by_cases h : Nat.Coprime d M <;> by_cases h' : Nat.Coprime d' M
    · rw [opF_inr_of_isUnit M d h, opF_inr_of_isUnit M d' h']; exact hDD _ _ f
    · rw [opF_inr_of_not_isUnit M d' h']; rfl
    · rw [opF_inr_of_not_isUnit M d h]; rfl
    · rw [opF_inr_of_not_isUnit M d h]; rfl

noncomputable def genD (i : Nat.Primes ⊕ ℕ) : Module.End ℂ (D M) := (opF M i).dualMap

theorem genD_apply (i : Nat.Primes ⊕ ℕ) (φ : D M) : genD M i φ = (opF M i).dualMap φ := rfl

theorem genD_comm (i j : Nat.Primes ⊕ ℕ) : genD M i * genD M j = genD M j * genD M i := by
  show (opF M i).dualMap ∘ₗ (opF M j).dualMap = (opF M j).dualMap ∘ₗ (opF M i).dualMap
  rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap]
  exact congrArg LinearMap.dualMap (opF_comm M j i)

theorem isMulCommutative_adjoin_genD : IsMulCommutative (Algebra.adjoin ℤ (Set.range (genD M))) :=
  Algebra.isMulCommutative_adjoin ℤ (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact genD_comm M i j)

set_option synthInstance.maxHeartbeats 1600000 in
open scoped IsMulCommutative in
noncomputable def ρDAux : HeckeAlgOne →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (genD M)) : Subalgebra ℤ (Module.End ℂ (D M))) :=
  haveI := isMulCommutative_adjoin_genD M
  MvPolynomial.aeval fun i => (⟨genD M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ : Algebra.adjoin ℤ (Set.range (genD M)))

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable def ρD : HeckeAlgOne →+* Module.End ℂ (D M) :=
  ((Algebra.adjoin ℤ (Set.range (genD M))).val.comp (ρDAux M)).toRingHom

theorem ρD_apply (t : HeckeAlgOne) : ρD M t = (ρDAux M t : Module.End ℂ (D M)) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
open scoped IsMulCommutative in
theorem ρDAux_X (i : Nat.Primes ⊕ ℕ) :
    ρDAux M (MvPolynomial.X i) = ⟨genD M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  haveI := isMulCommutative_adjoin_genD M
  MvPolynomial.aeval_X _ i

theorem ρD_X (i : Nat.Primes ⊕ ℕ) : ρD M (MvPolynomial.X i) = genD M i := by
  rw [ρD_apply, ρDAux_X]

theorem ρD_C (a : ℤ) : ρD M (MvPolynomial.C a) = (a : Module.End ℂ (D M)) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

end FC3B.Inst
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B"
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B"

namespace FC3B
namespace Inst

open ModularCurve
open scoped MatrixGroups

variable (M : ℕ) [NeZero M]

theorem hst_gen (i : Nat.Primes ⊕ ℕ) : ∀ v ∈ Λ M, genD M i v ∈ Λ M := by
  obtain ⟨hT, hU, hD⟩ := ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable M ⊥
  intro v hv
  rw [genD_apply]
  rcases i with ℓ | d
  · haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    by_cases h : (ℓ : ℕ) ∣ M
    · rw [opF_inl_of_dvd M ℓ h]; exact hU ℓ ℓ.2 h v hv
    · rw [opF_inl_of_not_dvd M ℓ h]; exact hT ℓ ℓ.2 h v hv
  · by_cases h : Nat.Coprime d M
    · rw [opF_inr_of_isUnit M d h]; exact hD _ v hv
    · rw [opF_inr_of_not_isUnit M d h, show (1 : Module.End ℂ (CuspForm (Γ M) 2)).dualMap = 1 from LinearMap.dualMap_id]; exact hv

theorem hst : ∀ (t : HeckeAlgOne), ∀ v ∈ Λ M, ρD M t v ∈ Λ M := by
  intro t
  induction t using MvPolynomial.induction_on with
  | C a => intro v hv; rw [ρD_C, Module.End.intCast_apply]; exact (Λ M).smul_mem a hv
  | add p q hp hq => intro v hv; rw [map_add, LinearMap.add_apply]; exact (Λ M).add_mem (hp v hv) (hq v hv)
  | mul_X p i hp => intro v hv; rw [map_mul, Module.End.mul_apply, ρD_X]; exact hp _ (hst_gen M i v hv)

theorem hspan {n : ℕ} (b : Module.Basis (Fin n) ℤ (Λ M))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ M) : D M)) = ⊤) (t : HeckeAlgOne)
    (h : ∀ i, ρD M t ((b i : Λ M) : D M) = 0) : ρD M t = 0 := by
  have key : (ρD M t).restrictScalars ℝ = 0 := by
    refine LinearMap.ext_on_range hsp fun i => ?_
    rw [LinearMap.restrictScalars_apply, h i, LinearMap.zero_apply]
  apply LinearMap.ext; intro v
  have := congrArg (fun F : D M →ₗ[ℝ] D M => F v) key
  simpa using this

theorem isDiamondAut_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) :
    IsDiamondAut M d = IsDiamondAut M d' := by
  have hc : Nat.Coprime d M ↔ Nat.Coprime d' M := by
    rw [← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime, h]
  funext σ
  apply propext
  simp only [IsDiamondAut, hc, h]

theorem diamondAut_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) : diamondAut M d = diamondAut M d' := by
  have key : ∀ P Q : (x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) → Prop, P = Q →
      (haveI := Classical.dec (∃ σ, P σ); if h : ∃ σ, P σ then h.choose else AlgEquiv.refl) =
        (haveI := Classical.dec (∃ σ, Q σ); if h : ∃ σ, Q σ then h.choose else AlgEquiv.refl) := by
    intro P Q hPQ; subst hPQ; rfl
  exact key _ _ (isDiamondAut_congr M h)

theorem diamondOneBar_congr {d d' : ℕ} (h : (d : ZMod M) = (d' : ZMod M)) :
    diamondOneBar M d = diamondOneBar M d' := by
  simp only [diamondOneBar, diamondAutBar, diamondAut_congr M h]

theorem isBaseChangeAutOf_diamondAutBar (d : ℕ) :
    IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) (diamondAutBar M d) := by
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (x1FunctionField M) (diamondAut M d).toRingEquiv
  exact isBaseChangeAutOf_baseChangeAut ⟨τ, fun y => hτ y⟩

theorem diamondAutBar_eq_refl_of_not_coprime {d : ℕ} (h : ¬ Nat.Coprime d M) :
    diamondAutBar M d = AlgEquiv.refl := by
  have hσ := isBaseChangeAutOf_diamondAutBar M d
  rw [diamondAut_of_not_coprime h] at hσ
  apply AlgEquiv.coe_algHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := AlgebraicClosure ℚ)
    (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' ((x1FunctionField M) : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  apply Subtype.ext
  exact hσ ⟨y, hy⟩

theorem diamondOneBar_eq_one_of_not_coprime (d : ℕ) (h : ¬ Nat.Coprime d M) : diamondOneBar M d = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [diamondOneBar_apply, diamondAutBar_eq_refl_of_not_coprime M h,
    show (AlgEquiv.refl : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M) = 1 from rfl,
    map_one, one_smul]
  rfl

theorem main (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ι : Type} (t : ι → ModularCurve.HeckeAlgOne)
    (hli : letI := ModularCurve.heckeModuleOneBar M
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlgOne (ModularCurve.JOne M)) (t i))) :
    letI := ModularCurve.heckeModuleOneBar M
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) (t i)) := by
  letI := ModularCurve.heckeModuleOneBar M
  have hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥ := ModularCurve.heckeDiamondInputsHAll M ⊥

  obtain ⟨hT, hU, hD⟩ := ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable M ⊥
  have hΓ : CongruenceSubgroup.IsCongruenceSubgroup (Γ M) := ⟨M, NeZero.ne _, CuspForm.Gamma_le_GammaH M ⊥⟩
  obtain ⟨n, b, -, hsp⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup (Γ M) hΓ
  obtain ⟨u, hinj, htors, huT, huU, huD⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf M ⊥ hinH hT hU hD
  have hbot : x1FunctionFieldBar M = xHFunctionFieldBar M ⊥ := by
    show laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionFieldC ℚ M) =
      laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionFieldC ℚ M ⊥)
    rw [xHFunctionFieldC_bot ℚ M]
  obtain ⟨heT, heD, -⟩ := ModularCurve.pic0Congr_jOne_jH_bot_compat M hin hinH hbot
  set e : JOne M ≃+ JH M ⊥ := AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq hbot).toRingEquiv
    (IntermediateField.equivOfEq hbot).commutes with he_def

  let u' : JOne M →+ D M ⧸ Λ M := u.comp e.toAddMonoidHom
  have hu'_apply : ∀ x, u' x = u (e x) := fun x => rfl
  have hinj' : Function.Injective u' := hinj.comp e.injective
  have htors' : ∀ y : D M ⧸ Λ M, IsOfFinAddOrder y → y ∈ u'.range := by
    intro y hy
    obtain ⟨z, hz⟩ := htors y hy
    exact ⟨e.symm z, by rw [hu'_apply, AddEquiv.apply_symm_apply, hz]⟩

  have hgen : ∀ (i : Nat.Primes ⊕ ℕ) (x : JOne M) (φ : D M),
      u' x = Submodule.Quotient.mk φ → u' ((MvPolynomial.X i : HeckeAlgOne) • x) = Submodule.Quotient.mk (genD M i φ) := by
    intro i x φ hx
    rw [hu'_apply] at hx ⊢
    rw [genD_apply]
    rcases i with ℓ | d
    · have heT' := heT ℓ.1 ℓ.2 x
      rw [show (⟨ℓ.1, ℓ.2⟩ : Nat.Primes) = ℓ from rfl] at heT'
      rw [show (MvPolynomial.X (Sum.inl ℓ) : HeckeAlgOne) = heckeGenOne ℓ from rfl,
        heckeModuleOneBar_heckeGenOne_smul hcomm, heT']
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      by_cases h : (ℓ : ℕ) ∣ M
      · rw [opF_inl_of_dvd M ℓ h]; exact huU ℓ.1 ℓ.2 h (e x) φ hx
      · rw [opF_inl_of_not_dvd M ℓ h]; exact huT ℓ.1 ℓ.2 h (e x) φ hx
    · rw [show (MvPolynomial.X (Sum.inr d) : HeckeAlgOne) = diamondGen d from rfl, heckeModuleOneBar_diamondGen_smul hcomm]
      by_cases h : Nat.Coprime d M
      · rw [opF_inr_of_isUnit M d h, heD d h]
        exact huD _ (e x) φ hx
      · rw [opF_inr_of_not_isUnit M d h, show (1 : Module.End ℂ (CuspForm (Γ M) 2)).dualMap = 1 from LinearMap.dualMap_id,
          diamondOneBar_eq_one_of_not_coprime M d h]
        exact hx

  have hu' : ∀ (s : HeckeAlgOne) (x : JOne M) (φ : D M),
      u' x = Submodule.Quotient.mk φ → u' (s • x) = Submodule.Quotient.mk (ρD M s φ) := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a =>
      intro x φ hx
      rw [heckeModuleOneBar_C_smul, map_zsmul, hx, ρD_C, Module.End.intCast_apply]
      show a • (Λ M).mkQ φ = (Λ M).mkQ (a • φ)
      rw [map_zsmul]
    | add p q hp hq =>
      intro x φ hx
      rw [add_smul, map_add, hp x φ hx, hq x φ hx, map_add, LinearMap.add_apply, Submodule.Quotient.mk_add]
    | mul_X p i hp =>
      intro x φ hx
      rw [mul_smul, map_mul, Module.End.mul_apply, ρD_X]
      exact hp _ _ (hgen i x φ hx)
  exact FC3B.Abstract.linearIndependent_rationalHeckeRepOne_of_uniformization p (JOne M) (Λ M) b (ρD M)
    (hst M) (hspan M b hsp) u' hinj' htors' hu' t hli

end FC3B.Inst
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B"
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B"

end
p2m_reactivate "P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B.Abstract P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.FC3B"

theorem solution (M p : ℕ) [NeZero M]
    [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ι : Type} (t : ι → ModularCurve.HeckeAlgOne)
    (hli : letI := ModularCurve.heckeModuleOneBar M
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlgOne (ModularCurve.JOne M)) (t i))) :
    letI := ModularCurve.heckeModuleOneBar M
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) (t i)) :=
  FC3B.Inst.main M p hin hcomm t hli

end S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent (solution)
