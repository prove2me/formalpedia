-- Prove2me | solution 1 for ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/85c441eb-3e42-5c15-b199-6da80da0e039

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf_complexConjugation
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
import Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups ComplexConjugate

namespace CHAJConjRed

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

variable (T : V →+ V) (hT : ∀ v ∈ Λ, T v ∈ Λ)

def quotEnd : V ⧸ Λ →+ V ⧸ Λ :=
  (Λ.mapQ Λ T.toIntLinearMap fun v hv => hT v hv).toAddMonoidHom

@[scoped simp] theorem quotEnd_mk (v : V) :
    quotEnd Λ T hT (Submodule.Quotient.mk v) = Submodule.Quotient.mk (T v) := rfl

theorem quotEnd_divLevel
    (hTp : ∀ (n : ℕ) (v : V), T ((((p : K) ^ n)⁻¹) • v) = (((p : K) ^ n)⁻¹) • T v) (n : ℕ) (v : V) :
    quotEnd Λ T hT (divLevel K p Λ n v) = divLevel K p Λ n (T v) := by
  rw [divLevel_apply, divLevel_apply, quotEnd_mk, hTp]

variable (TΛ : Λ →ₗ[ℤ] Λ)

theorem iota_restrict
    (hTp : ∀ (n : ℕ) (v : V), T ((((p : K) ^ n)⁻¹) • v) = (((p : K) ^ n)⁻¹) • T v)
    (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (l : Λ) :
    iota K p Λ (TΛ l) = tateMap p (quotEnd Λ T hT) (iota K p Λ l) :=
  Subtype.ext (funext fun n => by
    rw [coe_iota_apply, coe_tateMap_apply, coe_iota_apply, hTΛ, quotEnd_divLevel K p Λ T hT hTp])

theorem phi2_baseChange
    (hTp : ∀ (n : ℕ) (v : V), T ((((p : K) ^ n)⁻¹) • v) = (((p : K) ^ n)⁻¹) • T v)
    (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (z : ℤ_[p] ⊗[ℤ] Λ) :
    phi2 K p Λ b (TΛ.baseChange ℤ_[p] z) = tateMap p (quotEnd Λ T hT) (phi2 K p Λ b z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a l =>
      rw [LinearMap.baseChange_tmul, phi2_tmul, phi2_tmul, iota_restrict K p Λ T hT TΛ hTp hTΛ, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem assemble
    (hTp : ∀ (n : ℕ) (v : V), T ((((p : K) ^ n)⁻¹) • v) = (((p : K) ^ n)⁻¹) • T v)
    (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l)
    {M : Type} [AddCommGroup M] (u : M →+ V ⧸ Λ) (hu : Function.Injective u)
    (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range) (S : M →+ M)
    (hS : ∀ m, u (S m) = quotEnd Λ T hT (u m)) (x y : TateModule p M)
    (hy : ∀ n, (y : ℕ → M) n = S ((x : ℕ → M) n)) :
    ((tateEquivOfInjective u hu htors).trans (phi2 K p Λ b).symm) y =
      TΛ.baseChange ℤ_[p] (((tateEquivOfInjective u hu htors).trans (phi2 K p Λ b).symm) x) := by
  have hy' : y = tateMap p S x := Subtype.ext (funext hy)
  subst hy'
  apply (phi2 K p Λ b).injective
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
    phi2_baseChange K p Λ b T hT TΛ hTp hTΛ, LinearEquiv.apply_symm_apply,
    tateEquivOfInjective_apply, tateEquivOfInjective_apply]
  exact tateMap_naturality u S _ hS x

omit [Fintype ι] [DecidableEq ι] in

theorem liftBaseChange_eq_of_comp_eq (χ χ' : Λ →ₗ[ℤ] ℤ_[p]) (hkey : χ ∘ₗ TΛ = χ') (z : ℤ_[p] ⊗[ℤ] Λ) :
    χ'.liftBaseChange ℤ_[p] z = χ.liftBaseChange ℤ_[p] (TΛ.baseChange ℤ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, ← hkey,
      LinearMap.comp_apply]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

end Torus

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
  CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
    (CongruenceSubgroup.Gamma1_is_congruence M)

scoped instance finiteIndex_gammaH : (GammaH M H).FiniteIndex := (isCongruenceSubgroup_gammaH M H).finiteIndex

abbrev Lat : Submodule ℤ (Module.Dual ℂ (CuspForm (GammaH M H) 2)) := periodLatticeOf (GammaH M H)

def perL (δ : ↥(GammaH M H)) : ↥(Lat M H) :=
  ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩

@[scoped simp] theorem coe_perL (δ : ↥(GammaH M H)) : ((perL M H δ : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
    periodOf (GammaH M H) δ := rfl

theorem periodOf_mul (γ δ : ↥(GammaH M H)) :
    periodOf (GammaH M H) (γ * δ) = periodOf (GammaH M H) γ + periodOf (GammaH M H) δ := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.add_apply, ← periodMapOf_apply_eq_periodOf, ← periodMapOf_apply_eq_periodOf,
    ← periodMapOf_apply_eq_periodOf, ofMul_mul, map_add]

theorem periodOf_one : periodOf (GammaH M H) 1 = 0 := by
  have h := periodOf_mul M H 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

def perHom : H1 M H ↥(Lat M H) where
  toFun a := perL M H (Additive.toMul a)
  map_zero' := Subtype.ext (periodOf_one M H)
  map_add' a b := Subtype.ext (periodOf_mul M H (Additive.toMul a) (Additive.toMul b))

@[scoped simp] theorem perHom_apply (δ : ↥(GammaH M H)) : perHom M H (Additive.ofMul δ) = perL M H δ := rfl

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

theorem map_mem_of_forall {T : Module.Dual ℂ (CuspForm (GammaH M H) 2) →+ Module.Dual ℂ (CuspForm (GammaH M H) 2)}
    (hT : ∀ δ : ↥(GammaH M H), T (periodOf (GammaH M H) δ) ∈ Lat M H) :
    ∀ v ∈ Lat M H, T v ∈ Lat M H := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    exact hT δ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

theorem dualMap_mem_of_forall {T : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2}
    (hT : ∀ δ : ↥(GammaH M H), T.dualMap (periodOf (GammaH M H) δ) ∈ Lat M H) :
    ∀ v ∈ Lat M H, T.dualMap v ∈ Lat M H :=
  map_mem_of_forall M H (T := T.dualMap.toAddMonoidHom) hT

theorem dualMap_heckeTLinH_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∀ v ∈ Lat M H, (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ Lat M H :=
  dualMap_mem_of_forall M H fun δ => by
    rw [dualMap_heckeTLinH_periodOf]
    exact Subtype.mem _

theorem dualMap_heckeULinH_mem {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    ∀ v ∈ Lat M H, (CuspForm.heckeULinH (H := H) 2 q).dualMap v ∈ Lat M H :=
  dualMap_mem_of_forall M H fun δ => by
    rw [dualMap_heckeULinH_periodOf M H hq hqM]
    exact Subtype.mem _

theorem dualMap_diamondLinH_mem (d : (ZMod M)ˣ) :
    ∀ v ∈ Lat M H, (CuspForm.diamondLinH (H := H) 2 d).dualMap v ∈ Lat M H :=
  dualMap_mem_of_forall M H fun δ => by
    rw [dualMap_diamondLinH_periodOf]
    exact Subtype.mem _

theorem span_perL_eq_top : Submodule.span ℤ (Set.range (perL M H)) = ⊤ := by
  apply Submodule.map_injective_of_injective (Lat M H).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  rfl

variable (S : Set ℕ)

def genLin : Gen M S → (CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2)
  | .T _ hℓ _ hℓM => CuspForm.heckeTLinH 2 hℓ hℓM
  | .U q _ _ => CuspForm.heckeULinH 2 q
  | .dia d => CuspForm.diamondLinH 2 d

def TV (g : Gen M S) : Module.Dual ℂ (CuspForm (GammaH M H) 2) →ₗ[ℂ] Module.Dual ℂ (CuspForm (GammaH M H) 2) :=
  (genLin M H S g).dualMap

theorem TV_mem (g : Gen M S) : ∀ v ∈ Lat M H, (TV M H S g).toAddMonoidHom v ∈ Lat M H := by
  cases g with
  | T ℓ hℓ hℓS hℓM => exact dualMap_heckeTLinH_mem M H hℓ hℓM
  | U q hq hqM => exact dualMap_heckeULinH_mem M H hq hqM
  | dia d => exact dualMap_diamondLinH_mem M H d

variable {p : ℕ} [Fact p.Prime]

theorem TV_smul (g : Gen M S) (n : ℕ) (v : Module.Dual ℂ (CuspForm (GammaH M H) 2)) :
    (TV M H S g).toAddMonoidHom ((((p : ℂ) ^ n)⁻¹) • v) = (((p : ℂ) ^ n)⁻¹) • (TV M H S g).toAddMonoidHom v :=
  (TV M H S g).map_smul _ _

def TΛ (g : Gen M S) : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  ((TV M H S g).restrictScalars ℤ).restrict (TV_mem M H S g)

theorem coe_TΛ (g : Gen M S) (l : ↥(Lat M H)) :
    ((TΛ M H S g l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) = TV M H S g l := rfl

theorem chi_TΛ_perL (g : Gen M S) (ψ : H1 M H ℤ_[p]) (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ)) (δ : ↥(GammaH M H)) :
    χ (TΛ M H S g (perL M H δ)) = opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ) := by
  have hcomp : χ.toAddMonoidHom.comp (perHom M H) = ψ := by
    ext a
    exact hχ (Additive.toMul a)
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hval : TΛ M H S (.T ℓ hℓ hℓS hℓM) (perL M H δ) =
        heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
      Subtype.ext (dualMap_heckeTLinH_periodOf M H hℓ hℓM δ)
    rw [hval]
    show χ.toAddMonoidHom (heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
    rw [← AddMonoidHom.comp_apply, ← heckeT_comp, hcomp]
    rfl
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hval : TΛ M H S (.U q hq hqM) (perL M H δ) =
        heckeT M H q ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
      Subtype.ext (dualMap_heckeULinH_periodOf M H hq hqM δ)
    rw [hval]
    show χ.toAddMonoidHom (heckeT M H q ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
    rw [← AddMonoidHom.comp_apply, ← heckeT_comp, hcomp]
    rfl
  | dia d =>
    have hval : TΛ M H S (.dia d) (perL M H δ) =
        diamondRaw M H ↥(Lat M H) (CuspForm.gammaLift M d) (perHom M H) (Additive.ofMul δ) :=
      Subtype.ext (dualMap_diamondLinH_periodOf M H d δ)
    rw [hval]
    show χ.toAddMonoidHom (diamondRaw M H ↥(Lat M H) _ (perHom M H) (Additive.ofMul δ)) = _
    rw [← AddMonoidHom.comp_apply, ← diamondRaw_comp, hcomp]
    rfl

theorem chi_comp_TΛ_eq (g : Gen M S) (ψ : H1 M H ℤ_[p]) (χ χ' : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ))
    (hχ' : ∀ δ : ↥(GammaH M H), χ' (perL M H δ) = opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ)) :
    χ ∘ₗ TΛ M H S g = χ' := by
  refine LinearMap.ext_on_range (span_perL_eq_top M H) fun δ => ?_
  rw [LinearMap.comp_apply, chi_TΛ_perL M H S g ψ χ hχ, hχ']

end PeriodSide

section ConjSide

open CohCarrier ModularCurve UpperHalfPlane Matrix.SpecialLinearGroup

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_I, Complex.conj_I, neg_neg]

theorem J_smul_J_smul (τ : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

theorem J_smul_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.J • (γ • τ) = ModularCurve.Period.jConjSL γ • (UpperHalfPlane.J • τ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  have h := J_inv_mul_mapGL_mul_J γ
  rw [hJ] at h
  have h2 : UpperHalfPlane.J * (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) * UpperHalfPlane.J := by
    rw [← h, mul_assoc, mul_assoc, ← sq, UpperHalfPlane.J_sq, mul_one]
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, ← mul_smul]
  exact congrArg (· • τ) h2

theorem jStable : ∀ γ ∈ GammaH M H, ModularCurve.Period.jConjSL γ ∈ GammaH M H :=
  fun _ hγ => CohCarrier.jConjSL_mem_GammaH M H hγ

def conjF (f : CuspForm (GammaH M H) 2) : CuspForm (GammaH M H) 2 :=
  Classical.choose
    (CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (GammaH M H) (jStable M H) 2 f)

theorem conjF_apply (f : CuspForm (GammaH M H) 2) (τ : ℍ) :
    conjF M H f τ = conj (f (UpperHalfPlane.J • τ)) :=
  Classical.choose_spec
    (CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (GammaH M H) (jStable M H) 2 f) τ

theorem conjF_conjF (f : CuspForm (GammaH M H) 2) : conjF M H (conjF M H f) = f :=
  CuspForm.ext fun τ => by rw [conjF_apply, conjF_apply, Complex.conj_conj, J_smul_J_smul]

theorem conjF_eq_of_forall {f g : CuspForm (GammaH M H) 2}
    (hg : ∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) : conjF M H g = f :=
  CuspForm.ext fun τ => by rw [conjF_apply, hg, Complex.conj_conj, J_smul_J_smul]

theorem conjF_add (f g : CuspForm (GammaH M H) 2) : conjF M H (f + g) = conjF M H f + conjF M H g :=
  CuspForm.ext fun τ => by simp only [conjF_apply, CuspForm.add_apply, map_add]

theorem conjF_smul (a : ℂ) (f : CuspForm (GammaH M H) 2) : conjF M H (a • f) = conj a • conjF M H f :=
  CuspForm.ext fun τ => by
    rw [conjF_apply, CuspForm.IsGLPos.smul_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul, conjF_apply]

def Rdual (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) : Module.Dual ℂ (CuspForm (GammaH M H) 2) where
  toFun f := -conj (φ (conjF M H f))
  map_add' f g := by rw [conjF_add, map_add, map_add, neg_add]
  map_smul' a f := by
    show -conj (φ (conjF M H (a • f))) = a • (-conj (φ (conjF M H f)))
    rw [conjF_smul, LinearMap.map_smul, smul_eq_mul, map_mul, Complex.conj_conj, smul_eq_mul, mul_neg]

theorem Rdual_apply (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f : CuspForm (GammaH M H) 2) :
    Rdual M H φ f = -conj (φ (conjF M H f)) := rfl

def R : Module.Dual ℂ (CuspForm (GammaH M H) 2) →+ Module.Dual ℂ (CuspForm (GammaH M H) 2) where
  toFun := Rdual M H
  map_zero' := LinearMap.ext fun f => by
    rw [Rdual_apply, LinearMap.zero_apply, map_zero, neg_zero, LinearMap.zero_apply]
  map_add' φ ψ := LinearMap.ext fun f => by
    simp only [Rdual_apply, LinearMap.add_apply, map_add, neg_add]

theorem R_apply_apply (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f : CuspForm (GammaH M H) 2) :
    R M H φ f = -conj (φ (conjF M H f)) := rfl

theorem R_smul (a : ℂ) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) : R M H (a • φ) = conj a • R M H φ :=
  LinearMap.ext fun f => by
    rw [R_apply_apply, LinearMap.smul_apply, LinearMap.smul_apply, R_apply_apply, smul_eq_mul, smul_eq_mul,
      map_mul, mul_neg]

theorem R_R (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) : R M H (R M H φ) = φ :=
  LinearMap.ext fun f => by rw [R_apply_apply, R_apply_apply, map_neg, Complex.conj_conj, neg_neg, conjF_conjF]

variable {p : ℕ} [Fact p.Prime]

theorem R_inv_natCast_pow_smul (n : ℕ) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) :
    R M H ((((p : ℂ) ^ n)⁻¹) • φ) = (((p : ℂ) ^ n)⁻¹) • R M H φ := by
  rw [R_smul, map_inv₀, map_pow, map_natCast]

theorem R_pairing (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)) (f g : CuspForm (GammaH M H) 2)
    (hg : ∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) : R M H φ g = -conj (φ f) := by
  rw [R_apply_apply, conjF_eq_of_forall M H hg]

theorem eq_R_of_pairing (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2))
    (hpair : ∀ f g : CuspForm (GammaH M H) 2,
      (∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) → φ' g = -conj (φ f)) :
    φ' = R M H φ :=
  LinearMap.ext fun g => by
    rw [R_apply_apply]
    refine hpair (conjF M H g) g fun τ => ?_
    rw [conjF_apply, Complex.conj_conj, J_smul_J_smul]

theorem R_periodOf (δ : ↥(GammaH M H)) :
    R M H (periodOf (GammaH M H) δ) = periodOf (GammaH M H) (jConjGammaH M H δ) := by
  refine LinearMap.ext fun f => ?_
  rw [R_apply_apply]
  show -conj (periodAlongOf (GammaH M H) UpperHalfPlane.I ((δ : SL(2, ℤ)) • UpperHalfPlane.I) (conjF M H f)) =
    periodAlongOf (GammaH M H) UpperHalfPlane.I
      ((ModularCurve.Period.jConjSL (δ : SL(2, ℤ))) • UpperHalfPlane.I) f
  rw [ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (GammaH M H) f (conjF M H f)
      (conjF_apply M H f), map_neg, Complex.conj_conj, neg_neg, J_smul_sl_smul, J_smul_I]

theorem R_mem : ∀ v ∈ Lat M H, R M H v ∈ Lat M H :=
  map_mem_of_forall M H fun δ => by
    rw [R_periodOf]
    exact periodOf_mem_periodLatticeOf _ _

theorem partner_mem (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2))
    (hpair : ∀ f g : CuspForm (GammaH M H) 2,
      (∀ τ : ℍ, g τ = conj (f (UpperHalfPlane.J • τ))) → φ' g = -conj (φ f))
    (hφ : φ ∈ Lat M H) : φ' ∈ Lat M H := by
  rw [eq_R_of_pairing M H φ φ' hpair]
  exact R_mem M H φ hφ

def RΛ : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  (R M H).toIntLinearMap.restrict (p := Lat M H) (q := Lat M H) (R_mem M H)

theorem coe_RΛ (l : ↥(Lat M H)) :
    ((RΛ M H l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) = R M H l := rfl

theorem RΛ_perL (δ : ↥(GammaH M H)) : RΛ M H (perL M H δ) = perL M H (jConjGammaH M H δ) :=
  Subtype.ext (R_periodOf M H δ)

theorem chi_RΛ_perL (ψ : H1 M H ℤ_[p]) (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ)) (δ : ↥(GammaH M H)) :
    χ (RΛ M H (perL M H δ)) = charInvolution M H ℤ_[p] ℤ_[p] ψ (Additive.ofMul δ) := by
  rw [RΛ_perL, hχ, charInvolution_apply]
  rfl

theorem chi_comp_RΛ_eq (ψ : H1 M H ℤ_[p]) (χ χ' : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ))
    (hχ' : ∀ δ : ↥(GammaH M H), χ' (perL M H δ) = charInvolution M H ℤ_[p] ℤ_[p] ψ (Additive.ofMul δ)) :
    χ ∘ₗ RΛ M H = χ' := by
  refine LinearMap.ext_on_range (span_perL_eq_top M H) fun δ => ?_
  rw [LinearMap.comp_apply, chi_RΛ_perL M H ψ χ hχ, hχ']

end ConjSide

section Assembly

open CohCarrier ModularCurve

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

theorem uniformization_genOpH
    (u : JH M H →+ (Module.Dual ℂ (CuspForm (GammaH M H) 2) ⧸ periodLatticeOf (GammaH M H)))
    (hu_T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : JH M H) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ))
    (hu_U : ∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : JH M H) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ))
    (hu_D : ∀ (d : (ZMod M)ˣ) (x : JH M H) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (diamondHBar M H d x) = Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ))
    (g : Gen M S) (m : JH M H) :
    u (genOpH M H S g m) = quotEnd (Lat M H) (TV M H S g).toAddMonoidHom (TV_mem M H S g) (u m) := by
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective (Lat M H) (u m)
  rw [← hφ, quotEnd_mk]
  cases g with
  | T ℓ hℓ hℓS hℓM => exact hu_T ℓ hℓ hℓM m φ hφ.symm
  | U q hq hqM => exact hu_U q hq hqM m φ hφ.symm
  | dia d => exact hu_D d m φ hφ.symm

theorem uniformization_conj
    (u : JH M H →+ (Module.Dual ℂ (CuspForm (GammaH M H) 2) ⧸ periodLatticeOf (GammaH M H)))
    (hu_C : ∀ (x : JH M H) (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        (∀ f g : CuspForm (GammaH M H) 2,
          (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
            φ' g = -(starRingEnd ℂ) (φ f)) →
        u x = Submodule.Quotient.mk φ →
        u (complexConjugation • x) = Submodule.Quotient.mk φ')
    (m : JH M H) :
    u (DistribSMul.toAddMonoidHom (JH M H) complexConjugation m) =
      quotEnd (Lat M H) (R M H) (R_mem M H) (u m) := by
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective (Lat M H) (u m)
  rw [← hφ, quotEnd_mk]
  exact hu_C m φ (R M H φ) (R_pairing M H φ) hφ.symm

abbrev Tor : Type := Module.Dual ℂ (CuspForm (GammaH M H) 2) ⧸ periodLatticeOf (GammaH M H)

def eOf (u : JH M H →+ Tor M H) (hu_inj : Function.Injective u)
    (hu_tors : ∀ y, IsOfFinAddOrder y → y ∈ u.range) {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(Lat M H)) :
    TateModule p (JH M H) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥(Lat M H) :=
  (tateEquivOfInjective u hu_inj hu_tors).trans (phi2 ℂ p (Lat M H) b).symm

theorem clause_hecke (u : JH M H →+ Tor M H) (hu_inj : Function.Injective u)
    (hu_tors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (hu_T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : JH M H) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ))
    (hu_U : ∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : JH M H) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ))
    (hu_D : ∀ (d : (ZMod M)ˣ) (x : JH M H) (φ : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (diamondHBar M H d x) = Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ))
    {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(Lat M H))
    (g : Gen M S) (ψ : H1 M H ℤ_[p]) (χ χ' : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ))
    (hχ' : ∀ δ : ↥(GammaH M H), χ' (perL M H δ) = opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ))
    (x : TateModule p (JH M H)) :
    χ'.liftBaseChange ℤ_[p] (eOf M H p u hu_inj hu_tors b x) =
      χ.liftBaseChange ℤ_[p] (eOf M H p u hu_inj hu_tors b (ModularCurve.tateGenOpH M H S p g x)) := by
  have hcomm := assemble ℂ p (Lat M H) b (TV M H S g).toAddMonoidHom (TV_mem M H S g) (TΛ M H S g)
    (TV_smul M H S g) (fun _ => rfl) u hu_inj hu_tors (genOpH M H S g)
    (uniformization_genOpH M H S u hu_T hu_U hu_D g) x (ModularCurve.tateGenOpH M H S p g x) (fun _ => rfl)
  rw [eOf, hcomm]
  exact liftBaseChange_eq_of_comp_eq p (Lat M H) (TΛ M H S g) χ χ' (chi_comp_TΛ_eq M H S g ψ χ χ' hχ hχ') _

theorem clause_conj (u : JH M H →+ Tor M H) (hu_inj : Function.Injective u)
    (hu_tors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (hu_C : ∀ (x : JH M H) (φ φ' : Module.Dual ℂ (CuspForm (GammaH M H) 2)),
        (∀ f g : CuspForm (GammaH M H) 2,
          (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
            φ' g = -(starRingEnd ℂ) (φ f)) →
        u x = Submodule.Quotient.mk φ →
        u (complexConjugation • x) = Submodule.Quotient.mk φ')
    {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(Lat M H))
    (ψ : H1 M H ℤ_[p]) (χ χ' : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ))
    (hχ' : ∀ δ : ↥(GammaH M H), χ' (perL M H δ) = charInvolution M H ℤ_[p] ℤ_[p] ψ (Additive.ofMul δ))
    (x : TateModule p (JH M H)) :
    χ'.liftBaseChange ℤ_[p] (eOf M H p u hu_inj hu_tors b x) =
      χ.liftBaseChange ℤ_[p]
        (eOf M H p u hu_inj hu_tors b (ModularCurve.JH.tateGaloisRep M H p complexConjugation x)) := by
  have hcomm := assemble ℂ p (Lat M H) b (R M H) (R_mem M H) (RΛ M H)
    (R_inv_natCast_pow_smul M H) (fun _ => rfl) u hu_inj hu_tors
    (DistribSMul.toAddMonoidHom (JH M H) complexConjugation)
    (uniformization_conj M H u hu_C) x (ModularCurve.JH.tateGaloisRep M H p complexConjugation x)
    (fun _ => rfl)
  rw [eOf, hcomm]
  exact liftBaseChange_eq_of_comp_eq p (Lat M H) (RΛ M H) χ χ' (chi_comp_RΛ_eq M H ψ χ χ' hχ hχ') _

theorem mainThm (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ e : TateModule p (ModularCurve.JH M H) ≃ₗ[ℤ_[p]]
        ℤ_[p] ⊗[ℤ] ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (∀ (g : CohCarrier.Gen M S) (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              CohCarrier.opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p] (e (ModularCurve.tateGenOpH M H S p g x))) ∧
      (∀ (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              CohCarrier.charInvolution M H ℤ_[p] ℤ_[p] ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p]
                (e (ModularCurve.JH.tateGaloisRep M H p complexConjugation x))) := by

  obtain ⟨u, hu_inj, hu_tors, hu_T, hu_U, hu_D, hu_C⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf_complexConjugation
      M H hin
      (fun ℓ hℓ hℓM => dualMap_heckeTLinH_mem M H hℓ hℓM) (fun q hq hqM => dualMap_heckeULinH_mem M H hq hqM)
      (dualMap_diamondLinH_mem M H) (partner_mem M H)

  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH M H) (isCongruenceSubgroup_gammaH M H)
  exact ⟨eOf M H p u hu_inj hu_tors b,
    fun g ψ _ χ χ' hχ hχ' x => clause_hecke M H S p u hu_inj hu_tors hu_T hu_U hu_D b g ψ χ χ' hχ hχ' x,
    fun ψ _ χ χ' hχ hχ' x => clause_conj M H p u hu_inj hu_tors hu_C b ψ χ χ' hχ hχ' x⟩

end Assembly

end CHAJConjRed
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution.CHAJConjRed"

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ e : TateModule p (ModularCurve.JH M H) ≃ₗ[ℤ_[p]]
        ℤ_[p] ⊗[ℤ] ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (∀ (g : CohCarrier.Gen M S) (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              CohCarrier.opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p] (e (ModularCurve.tateGenOpH M H S p g x))) ∧
      (∀ (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              CohCarrier.charInvolution M H ℤ_[p] ℤ_[p] ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p]
                (e (ModularCurve.JH.tateGaloisRep M H p complexConjugation x))) :=
  CHAJConjRed.mainThm M H S p hin

end
end S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
end P2MW
export P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution (solution)
