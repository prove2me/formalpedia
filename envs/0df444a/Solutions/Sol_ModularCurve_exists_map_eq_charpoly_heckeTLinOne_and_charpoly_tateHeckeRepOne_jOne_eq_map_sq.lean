-- Prove2me | solution 1 for ModularCurve.exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d3c1052e-a91a-5ae2-b89d-79e8d2829e60

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CohCarrier_CharInvolution
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_heckeDiamondCommuteBar
import Theorems.Thm_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z"
p2m_attr_erase "instance" "ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups ModularForm ComplexConjugate

namespace ESCharpolyJOne

section Generic

p2m_open "ModularCurve AlgebraicCurve~H1 IntermediateField HahnSeries CongruenceSubgroup"
open scoped MatrixGroups

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem coeffMap_qExpandG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem coeffEmb_qExpandG (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpandG _ n x

variable (L) in
theorem laurentBaseChange_monoG {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem qExpand_mem_laurentBaseChangeG {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpandG]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

variable (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [NeZero ℓ]

abbrev botF : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ Γ

abbrev topF : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))

omit [NeZero ℓ] in
theorem botF_le_topF : botF Γ ≤ topF M Γ ℓ := qExpFunctionFieldC_mono ℚ inf_le_left

variable (L) in

def alphaG : laurentBaseChange L (botF Γ) →ₐ[L] laurentBaseChange L (topF M Γ ℓ) :=
  IntermediateField.inclusion (laurentBaseChange_monoG L (botF_le_topF M Γ ℓ))

def BetaDefinedG : Prop := ∀ y ∈ botF Γ, qExpand ℚ ℓ y ∈ topF M Γ ℓ

variable (L) in

def betaRingHomOfG (h : BetaDefinedG M Γ ℓ) :
    laurentBaseChange L (botF Γ) →+* laurentBaseChange L (topF M Γ ℓ) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChangeG ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in

def betaOfG (h : BetaDefinedG M Γ ℓ) :
    laurentBaseChange L (botF Γ) →ₐ[L] laurentBaseChange L (topF M Γ ℓ) :=
  { betaRingHomOfG L M Γ ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

open Classical in
variable (L) in

def betaG : laurentBaseChange L (botF Γ) →ₐ[L] laurentBaseChange L (topF M Γ ℓ) :=
  if h : BetaDefinedG M Γ ℓ then betaOfG L M Γ ℓ h else alphaG L M Γ ℓ

variable (L) in

def AlphaIntegralG : Prop := (alphaG L M Γ ℓ).toRingHom.IsIntegral
variable (L) in

def BetaIntegralG : Prop := (betaG L M Γ ℓ).toRingHom.IsIntegral

variable {M Γ ℓ}

def pic0G (hα : AlphaIntegralG L M Γ ℓ) (hβ : BetaIntegralG L M Γ ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (topF M Γ ℓ))]
    (hFI : FundamentalIdentityAlong L (betaG L M Γ ℓ) hβ)
    (hfin : FiniteAlong L (alphaG L M Γ ℓ))
    (hN : NormFormulaAlong L (alphaG L M Γ ℓ) hfin) :
    Pic0 L (laurentBaseChange L (botF Γ)) →+ Pic0 L (laurentBaseChange L (botF Γ)) :=
  Pic0.correspondence (betaG L M Γ ℓ) (alphaG L M Γ ℓ) hβ hα hFI hfin hN

variable (L M Γ ℓ)

def InputsG : Prop :=
  ∃ (_ : BetaDefinedG M Γ ℓ) (_ : AlphaIntegralG L M Γ ℓ) (hβ : BetaIntegralG L M Γ ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (topF M Γ ℓ)))
    (hfin : FiniteAlong L (alphaG L M Γ ℓ)),
    FundamentalIdentityAlong L (betaG L M Γ ℓ) hβ ∧ NormFormulaAlong L (alphaG L M Γ ℓ) hfin

open Classical in

def opG : Pic0 L (laurentBaseChange L (botF Γ)) →+ Pic0 L (laurentBaseChange L (botF Γ)) :=
  if h : InputsG L M Γ ℓ then
    haveI := h.snd.snd.snd.fst
    pic0G h.snd.fst h.snd.snd.fst h.snd.snd.snd.snd.snd.1 h.snd.snd.snd.snd.fst h.snd.snd.snd.snd.snd.2
  else 0

theorem heckeOperatorOneAlong_eq_opG : heckeOperatorOneAlong L M ℓ = opG L M (Gamma1 M) ℓ := rfl

theorem heckeOperatorHAlong_eq_opG (H : Subgroup (ZMod M)ˣ) :
    heckeOperatorHAlong L M H ℓ = opG L M (CohCarrier.GammaH M H) ℓ := rfl

abbrev JG (Γ : Subgroup SL(2, ℤ)) : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (botF Γ))

example : JOne M = JG (Gamma1 M) := rfl
example (H : Subgroup (ZMod M)ˣ) : JH M H = JG (CohCarrier.GammaH M H) := rfl

variable (p : ℕ) [Fact p.Prime]

def tateOpG : Module.End ℤ_[p] (TateModule p (JG Γ)) :=
  TateModule.rep p (JG Γ) (AddMonoid.End (JG Γ)) (opG (AlgebraicClosure ℚ) M Γ ℓ)

theorem tateGenOpH_eq_tateOpG (H : Subgroup (ZMod M)ˣ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (∅ : Set ℕ))
    (hℓM : ¬ ℓ ∣ M) :
    tateGenOpH M H ∅ p (.T ℓ hℓ hℓS hℓM) = tateOpG M (CohCarrier.GammaH M H) ℓ p := rfl

theorem tateHeckeRepOne_eq_tateOpG [NeZero M] (hcomm : HeckeDiamondCommuteBar M) (hℓ : ℓ.Prime) :
    letI := heckeModuleOneBar M
    tateHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, hℓ⟩) = tateOpG M (Gamma1 M) ℓ p := by
  letI := heckeModuleOneBar M
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  change (heckeGenOne ⟨ℓ, hℓ⟩ : HeckeAlgOne) • (x : ℕ → JOne M) n =
    heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ ((x : ℕ → JOne M) n)
  rw [heckeModuleOneBar_heckeGenOne_smul hcomm]
  rfl

theorem charpoly_tateOpG_eq_of_eq {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ = Γ') (P : Polynomial ℤ_[p])
    [Module.Finite ℤ_[p] (TateModule p (JG Γ))] [Module.Free ℤ_[p] (TateModule p (JG Γ))]
    [Module.Finite ℤ_[p] (TateModule p (JG Γ'))] [Module.Free ℤ_[p] (TateModule p (JG Γ'))]
    (hP : (tateOpG M Γ ℓ p).charpoly = P) : (tateOpG M Γ' ℓ p).charpoly = P := by
  subst h
  exact hP

omit [NeZero ℓ] in
theorem moduleFinite_of_eq {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ = Γ')
    [Module.Finite ℤ_[p] (TateModule p (JG Γ'))] : Module.Finite ℤ_[p] (TateModule p (JG Γ)) := by
  subst h; infer_instance

omit [NeZero ℓ] in
theorem moduleFree_of_eq {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ = Γ')
    [Module.Free ℤ_[p] (TateModule p (JG Γ'))] : Module.Free ℤ_[p] (TateModule p (JG Γ)) := by
  subst h; infer_instance

omit [NeZero ℓ] in

theorem exists_linearEquiv_cuspForm_of_eq {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ = Γ') (k : ℤ) :
    ∃ E : CuspForm Γ k ≃ₗ[ℂ] CuspForm Γ' k, ∀ f, ⇑(E f) = ⇑f := by
  subst h
  exact ⟨LinearEquiv.refl ℂ _, fun _ => rfl⟩

end Generic

section Reality

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem charpoly_map_conj_eq (T : V →ₗ[ℂ] V) (c : V →+ V)
    (hc : ∀ (a : ℂ) (v : V), c (a • v) = conj a • c v) (hcc : ∀ v, c (c v) = v)
    (hT : ∀ v, c (T v) = T (c v)) : T.charpoly.map (starRingEnd ℂ) = T.charpoly := by
  classical
  let b := Module.finBasis ℂ V
  set n := Module.finrank ℂ V

  have hli : LinearIndependent ℂ (fun i => c (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : c (∑ j, g j • c (b j)) = ∑ j, conj (g j) • b j := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hc, hcc]
    rw [hg, map_zero] at h1
    have h2 := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at h2
    have := h2 (fun j => conj (g j)) h1.symm i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => c (b i)) := by
    intro v _
    have hv : v = ∑ i, conj (b.repr (c v) i) • c (b i) := by
      conv_lhs => rw [← hcc v, ← b.sum_repr (c v)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hc]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin n) ℂ V := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = c (b i) := fun i => Module.Basis.mk_apply hli hsp i

  have hmat : LinearMap.toMatrix b' b' T = (LinearMap.toMatrix b b T).map (starRingEnd ℂ) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb']
    have hTb : T (b j) = ∑ i, b.repr (T (b j)) i • b i := (b.sum_repr (T (b j))).symm
    have : T (c (b j)) = ∑ i, conj (b.repr (T (b j)) i) • b' i := by
      rw [← hT]
      conv_lhs => rw [hTb, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hc, hb']
    rw [this, b'.repr_sum_self]
  conv_rhs => rw [← LinearMap.charpoly_toMatrix T b', hmat, Matrix.charpoly_map]
  rw [← LinearMap.charpoly_toMatrix T b]

end Abstract

section Concrete

open UpperHalfPlane CohCarrier ModularCurve.Period Matrix.SpecialLinearGroup CongruenceSubgroup

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)

local notation "ΓGL" => ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem val_mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem val_J_apply (i j : Fin 2) :
    ((J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  rw [val_J]

theorem J_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    J * (mapGL ℝ γ : GL (Fin 2) ℝ) * J = mapGL ℝ (jConjSL γ) := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, val_mapGL_apply, val_J_apply]
  fin_cases i <;> fin_cases j <;> simp [jConjMat]

theorem J_mul_J : (J : GL (Fin 2) ℝ) * J = 1 := by
  rw [← sq, J_sq]

theorem J_inv : (J : GL (Fin 2) ℝ)⁻¹ = J :=
  inv_eq_of_mul_eq_one_right J_mul_J

omit [NeZero M] in
open ConjAct Pointwise in
theorem gammaGL_eq_conj : ΓGL = toConjAct (J : GL (Fin 2) ℝ)⁻¹ • ΓGL := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul, J_inv]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [J_mul_mapGL_mul_J]
    exact ⟨_, jConjSL_mem_GammaH M H hγ, rfl⟩
  · rintro ⟨γ, hγ, hx⟩
    have : x = J * mapGL ℝ γ * J := by
      rw [hx, ← mul_assoc, ← mul_assoc, J_mul_J, one_mul, mul_assoc, J_mul_J, mul_one]
    rw [this, J_mul_mapGL_mul_J]
    exact ⟨_, jConjSL_mem_GammaH M H hγ, rfl⟩

def conjF (f : CuspForm ΓGL k) : CuspForm ΓGL k :=
  (CuspForm.translate f J).copy (⇑f ∣[k] J) rfl (gammaGL_eq_conj M H)

@[scoped simp] theorem coe_conjF (f : CuspForm ΓGL k) : ⇑(conjF M H k f) = ⇑f ∣[k] J := rfl

def conjAdd : CuspForm ΓGL k →+ CuspForm ΓGL k where
  toFun := conjF M H k
  map_zero' := DFunLike.coe_injective <| by
    show ⇑(0 : CuspForm ΓGL k) ∣[k] J = ⇑(0 : CuspForm ΓGL k)
    rw [CuspForm.coe_zero]; exact SlashAction.zero_slash k J
  map_add' f g := DFunLike.coe_injective <| by
    simp only [coe_conjF, CuspForm.coe_add, SlashAction.add_slash]

theorem conjAdd_smul (a : ℂ) (f : CuspForm ΓGL k) :
    conjAdd M H k (a • f) = conj a • conjAdd M H k f := DFunLike.coe_injective <| by
  show ⇑(a • f) ∣[k] J = ⇑(conj a • conjF M H k f)
  rw [CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, coe_conjF, ModularForm.smul_slash, sigma_J]
  rfl

theorem conjAdd_conjAdd (f : CuspForm ΓGL k) : conjAdd M H k (conjAdd M H k f) = f :=
  DFunLike.coe_injective <| by
    show (⇑f ∣[k] J) ∣[k] J = ⇑f
    rw [← SlashAction.slash_mul, J_mul_J, SlashAction.slash_one]

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)

theorem slash_mapGL_of_mem (f : CuspForm ΓGL k) {γ : SL(2, ℤ)} (hγ : γ ∈ GammaH M H) :
    ⇑f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

omit [NeZero M] in

theorem J_mul_heckeMatrix (j j' : ℕ) (n : ℤ) (h : (j' : ℤ) + n * ℓ = -j) (hℓ0 : ℓ ≠ 0) :
    J * ModularForm.heckeMatrix ℓ j =
      (mapGL ℝ (ModularGroup.T ^ n) : GL (Fin 2) ℝ) * ModularForm.heckeMatrix ℓ j' * J := by
  have h' : (j' : ℝ) + n * ℓ = -j := by exact_mod_cast h
  have hT : ∀ i i' : Fin 2, ((ModularGroup.T ^ n : SL(2, ℤ)) i i' : ℤ) =
      (!![(1 : ℤ), n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i i' := fun i i' => by
    rw [← ModularGroup.coe_T_zpow n]
  ext i i'
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, val_mapGL_apply, val_J_apply, hT,
    ModularForm.val_heckeMatrix hℓ0]
  fin_cases i <;> fin_cases i' <;> simp
  linarith

include hℓ in

theorem heckeU_slash_J (f : CuspForm ΓGL k) :
    (ModularForm.heckeU k ℓ ⇑f) ∣[k] J = ModularForm.heckeU k ℓ (⇑f ∣[k] J) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [CuspForm.Gamma1Hecke.heckeU_eq_sum_zmod, CuspForm.Gamma1Hecke.heckeU_eq_sum_zmod,
    SlashAction.sum_slash]

  rw [← Equiv.sum_comp (Equiv.neg (ZMod ℓ))]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.neg_apply]

  have hdvd : (ℓ : ℤ) ∣ -(((-x).val : ℕ) : ℤ) - (x.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, neg_neg, sub_self]
  obtain ⟨n, hn⟩ := hdvd
  have h : (((-x).val : ℕ) : ℤ) + n * ℓ = -((x.val : ℕ) : ℤ) := by linarith [hn, mul_comm n (ℓ : ℤ)]
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul,
    J_mul_heckeMatrix x.val ((-x).val) n h hℓ.ne_zero, SlashAction.slash_mul, SlashAction.slash_mul,
    SlashAction.slash_mul,
    slash_mapGL_of_mem M H k f (Subgroup.zpow_mem _ (ModularCurve.translation_mem_GammaH M H) n)]

omit [NeZero M] in

theorem mapGL_mul_diag_mul_J (ρ : SL(2, ℤ)) (hℓ0 : ℓ ≠ 0) :
    (mapGL ℝ ρ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ * J =
      J * ((mapGL ℝ (jConjSL ρ) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
  ext i i'
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, val_mapGL_apply, val_J_apply,
    ModularForm.val_heckeDiagMatrix hℓ0]
  fin_cases i <;> fin_cases i' <;> simp [jConjMat]

theorem conjAdd_heckeTLinH (f : CuspForm ΓGL k) :
    conjAdd M H k (CuspForm.heckeTLinH k hℓ hℓM f) = CuspForm.heckeTLinH k hℓ hℓM (conjAdd M H k f) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hT := CuspForm.stableT M H k hℓ hℓM
  set ρ : Gamma0 M := CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) with hρdef
  have hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := CuspForm.gammaLift_apply_11 hℓ hℓM
  let ρ' : Gamma0 M := ⟨jConjSL (ρ : SL(2, ℤ)), jConjSL_mem_Gamma0 ρ.2⟩
  have h11 : (jConjSL (ρ : SL(2, ℤ)) : SL(2, ℤ)) 1 1 = (ρ : SL(2, ℤ)) 1 1 := jConjMat_apply_one_one _
  have hρ' : (((ρ' : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
    show (((jConjSL (ρ : SL(2, ℤ)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ
    rw [h11]
    exact hρ
  refine DFunLike.coe_injective ?_
  show ⇑(CuspForm.heckeTLinH k hℓ hℓM f) ∣[k] J = ⇑(CuspForm.heckeTLinH k hℓ hℓM (conjF M H k f))
  rw [CuspForm.coe_heckeTLinH_apply k hℓ hℓM hT f, CuspForm.coe_heckeTLinH_eq k hℓ hℓM hT ρ' hρ',
    coe_conjF, SlashAction.add_slash, heckeU_slash_J M H k hℓ, ← SlashAction.slash_mul,
    ← hρdef, mapGL_mul_diag_mul_J ρ hℓ.ne_zero, SlashAction.slash_mul]

theorem charpoly_heckeTLinH_real [FiniteDimensional ℂ (CuspForm ΓGL k)] :
    (CuspForm.heckeTLinH (H := H) k hℓ hℓM).charpoly.map (starRingEnd ℂ) =
      (CuspForm.heckeTLinH (H := H) k hℓ hℓM).charpoly :=
  charpoly_map_conj_eq _ (conjAdd M H k) (conjAdd_smul M H k) (conjAdd_conjAdd M H k)
    (conjAdd_heckeTLinH M H k hℓ hℓM)

end Concrete

end Reality

section LevelH

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

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)

abbrev Tan : CuspForm (GammaH M H) 2 →ₗ[ℂ] CuspForm (GammaH M H) 2 := CuspForm.heckeTLinH 2 hℓ hℓM

theorem periodMapOf_heckeTLinH (f : CuspForm (GammaH M H) 2) :
    periodMapOf (GammaH M H) (Tan M H hℓ hℓM f) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ℂ (periodMapOf (GammaH M H) f)) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM) f _
    (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

theorem dualMap_heckeTLinH_periodOf (δ : ↥(GammaH M H)) :
    (Tan M H hℓ hℓM).dualMap (periodOf (GammaH M H) δ) =
      (((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M H ℓ ↥(Lat M H) (perHom M H)) (Additive.ofMul δ) : ↥(Lat M H)) :
        Module.Dual ℂ (CuspForm (GammaH M H) 2)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.dualMap_apply, ← periodMapOf_apply_eq_periodOf, periodMapOf_heckeTLinH,
    ← evalL_comp_perHom, heckeT_comp]
  rfl

theorem dualMap_mem : ∀ v ∈ Lat M H, (Tan M H hℓ hℓM).dualMap v ∈ Lat M H := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    rw [dualMap_heckeTLinH_periodOf]
    exact Subtype.mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ n hx

def tauT : ↥(Lat M H) →ₗ[ℤ] ↥(Lat M H) :=
  (((Tan M H hℓ hℓM).dualMap).restrictScalars ℤ).restrict (dualMap_mem M H hℓ hℓM)

theorem coe_tauT (l : ↥(Lat M H)) :
    ((tauT M H hℓ hℓM l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
      (Tan M H hℓ hℓM).dualMap l := rfl

theorem coe_tauT' (l : ↥(Lat M H)) :
    ((tauT M H hℓ hℓM l : ↥(Lat M H)) : Module.Dual ℂ (CuspForm (GammaH M H) 2)) =
      (l : Module.Dual ℂ (CuspForm (GammaH M H) 2)) ∘ₗ Tan M H hℓ hℓM := rfl

variable {p : ℕ} [Fact p.Prime]

abbrev genT : Gen M (∅ : Set ℕ) := .T ℓ hℓ (Set.notMem_empty ℓ) hℓM

theorem chi_tauT_perL (ψ : H1 M H ℤ_[p]) (χ : ↥(Lat M H) →ₗ[ℤ] ℤ_[p])
    (hχ : ∀ δ : ↥(GammaH M H), χ (perL M H δ) = ψ (Additive.ofMul δ)) (δ : ↥(GammaH M H)) :
    χ (tauT M H hℓ hℓM (perL M H δ)) = opFamily M H ∅ ℤ_[p] (genT M hℓ hℓM) ψ (Additive.ofMul δ) := by
  have hcomp : χ.toAddMonoidHom.comp (perHom M H) = ψ := by
    ext a
    exact hχ (Additive.toMul a)
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hval : tauT M H hℓ hℓM (perL M H δ) = heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ) :=
    Subtype.ext (dualMap_heckeTLinH_periodOf M H hℓ hℓM δ)
  rw [hval]
  show χ.toAddMonoidHom (heckeT M H ℓ ↥(Lat M H) (perHom M H) (Additive.ofMul δ)) = _
  rw [← AddMonoidHom.comp_apply, ← heckeT_comp, hcomp]
  rfl

theorem key [Module.Free ℤ ↥(Lat M H)]
    (e : TateModule p (JH M H) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] ↥(Lat M H))
    (he : ∀ (g : Gen M (∅ : Set ℕ)) (ψ : H1 M H ℤ_[p]),
        ψ ∈ Period.parabolicHoms ℤ_[p] (GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ↥(Lat M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : ↥(GammaH M H), χ ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : ↥(GammaH M H), χ' ⟨periodOf (GammaH M H) δ, periodOf_mem_periodLatticeOf (GammaH M H) δ⟩ =
              opFamily M H ∅ ℤ_[p] g ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) = χ.liftBaseChange ℤ_[p] (e (tateGenOpH M H ∅ p g x)))
    (x : TateModule p (JH M H)) :
    e (tateGenOpH M H ∅ p (genT M hℓ hℓM) x) = (tauT M H hℓ hℓM).baseChange ℤ_[p] (e x) := by
  refine eq_of_forall_liftBaseChange_eq ℤ_[p] fun χ => ?_
  have h := he (genT M hℓ hℓM) (χ.toAddMonoidHom.comp (perHom M H)) (comp_perHom_mem_parabolicHoms M H ℤ_[p] _)
    χ (χ ∘ₗ tauT M H hℓ hℓM) (fun δ => rfl)
    (fun δ => chi_tauT_perL M H hℓ hℓM _ χ (fun _ => rfl) δ) x
  rw [liftBaseChange_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem mainH [FiniteDimensional ℂ (CuspForm (GammaH M H) 2)]
    [Module.Finite ℤ_[p] (TateModule p (JH M H))] [Module.Free ℤ_[p] (TateModule p (JH M H))]
    (hreal : (Tan M H hℓ hℓM).charpoly.map (starRingEnd ℂ) = (Tan M H hℓ hℓM).charpoly) :
    ∃ Q : Polynomial ℤ, Q.Monic ∧ Q.map (algebraMap ℤ ℂ) = (Tan M H hℓ hℓM).charpoly ∧
      (tateGenOpH M H ∅ p (genT M hℓ hℓM)).charpoly = (Q ^ 2).map (algebraMap ℤ ℤ_[p]) := by
  obtain ⟨n, b, hli, hsp⟩ :=
    exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (GammaH M H) (isCongruenceSubgroup_gammaH M H)
  haveI : Module.Free ℤ ↥(Lat M H) := Module.Free.of_basis b
  haveI : Module.Finite ℤ ↥(Lat M H) := Module.Finite.of_basis b
  obtain ⟨Q, hQm, hQmap, hτ⟩ :=
    Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
      (Tan M H hℓ hℓM) hreal (Lat M H) b hli hsp (tauT M H hℓ hℓM) (fun x => rfl)
  refine ⟨Q, hQm, hQmap, ?_⟩
  obtain ⟨e, he⟩ := exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
    M p H (∅ : Set ℕ) (heckeDiamondInputsHAll M H)
  have hconj : e.conj (tateGenOpH M H ∅ p (genT M hℓ hℓM)) = (tauT M H hℓ hℓM).baseChange ℤ_[p] := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, key M H hℓ hℓM e he, LinearEquiv.apply_symm_apply]
  rw [← LinearEquiv.charpoly_conj e, hconj, LinearMap.charpoly_baseChange, hτ]

end PeriodSide

end LevelH

section Assembly

open ModularCurve CohCarrier CongruenceSubgroup

theorem mainOne (M p : ℕ) [NeZero M] [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    [FiniteDimensional ℂ (CuspForm (Gamma1 M) 2)]
    [Module.Finite ℤ_[p] (TateModule p (JOne M))]
    [Module.Free ℤ_[p] (TateModule p (JOne M))] :
    letI := heckeModuleOneBar M
    ∃ Q : Polynomial ℤ, Q.Monic ∧
      Q.map (algebraMap ℤ ℂ) = (CuspForm.heckeTLinOne 2 hℓ hℓM).charpoly ∧
      (tateHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, hℓ⟩)).charpoly = (Q ^ 2).map (algebraMap ℤ ℤ_[p]) := by
  letI := heckeModuleOneBar M
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hbot : GammaH M ⊥ = Gamma1 M := GammaH_bot M

  haveI j1 : Module.Finite ℤ_[p] (TateModule p (JG (Gamma1 M))) := ‹Module.Finite ℤ_[p] (TateModule p (JOne M))›
  haveI j2 : Module.Free ℤ_[p] (TateModule p (JG (Gamma1 M))) := ‹Module.Free ℤ_[p] (TateModule p (JOne M))›
  haveI iF' : Module.Finite ℤ_[p] (TateModule p (JG (GammaH M ⊥))) := moduleFinite_of_eq p hbot
  haveI iFr' : Module.Free ℤ_[p] (TateModule p (JG (GammaH M ⊥))) := moduleFree_of_eq p hbot
  haveI iF : Module.Finite ℤ_[p] (TateModule p (JH M ⊥)) := iF'
  haveI iFr : Module.Free ℤ_[p] (TateModule p (JH M ⊥)) := iFr'
  obtain ⟨E, hE⟩ := exists_linearEquiv_cuspForm_of_eq hbot 2
  haveI : FiniteDimensional ℂ (CuspForm (GammaH M ⊥) 2) := LinearEquiv.finiteDimensional E.symm

  have hreal := charpoly_heckeTLinH_real M ⊥ 2 hℓ hℓM
  obtain ⟨Q, hQm, hQC, hQT⟩ := mainH M ⊥ hℓ hℓM (p := p) hreal
  refine ⟨Q, hQm, ?_, ?_⟩
  ·
    have hE' : ∀ g : CuspForm (Gamma1 M) 2, ⇑(E.symm g) = ⇑g := fun g => by
      rw [← hE (E.symm g), LinearEquiv.apply_symm_apply]
    have hT := CuspForm.stableT M ⊥ 2 hℓ hℓM
    set ρ : Gamma0 M := CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) with hρdef
    have hρ : CuspForm.IsDiamondLift M ℓ (ρ : SL(2, ℤ)) := ⟨ρ.2, CuspForm.gammaLift_apply_11 hℓ hℓM⟩
    have hconj : E.conj (Tan M ⊥ hℓ hℓM) = CuspForm.heckeTLinOne 2 hℓ hℓM := by
      refine LinearMap.ext fun g => DFunLike.coe_injective ?_
      show ⇑(E.conj (Tan M ⊥ hℓ hℓM) g) = ⇑(CuspForm.heckeTLinOne 2 hℓ hℓM g)
      rw [LinearEquiv.conj_apply_apply, hE, CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM hT, hE',
        CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift 2 hℓ hℓM hρ, SlashAction.slash_mul]
    rw [hQC, ← hconj, LinearEquiv.charpoly_conj]
  ·
    rw [tateGenOpH_eq_tateOpG] at hQT
    have h1 := charpoly_tateOpG_eq_of_eq M ℓ p hbot _ hQT
    rw [tateHeckeRepOne_eq_tateOpG M ℓ p (heckeDiamondCommuteBar M) hℓ]
    exact h1

end Assembly

end ESCharpolyJOne
p2m_reactivate "P2MW.S_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq.ESCharpolyJOne"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq.ESCharpolyJOne"

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    [FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2)]
    [Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne M))]
    [Module.Free ℤ_[p] (TateModule p (ModularCurve.JOne M))] :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ Q : Polynomial ℤ, Q.Monic ∧
      Q.map (algebraMap ℤ ℂ) = (CuspForm.heckeTLinOne 2 hℓ hℓM).charpoly ∧
      (ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
          (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).charpoly = (Q ^ 2).map (algebraMap ℤ ℤ_[p]) :=
  ESCharpolyJOne.mainOne M p hℓ hℓM

end S_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq
end P2MW
export P2MW.S_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq (solution)
