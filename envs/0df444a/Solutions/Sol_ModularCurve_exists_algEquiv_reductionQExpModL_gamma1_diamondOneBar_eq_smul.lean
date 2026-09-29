-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/cfe3a0f9-dc57-5d30-ab06-fab8f790ffca

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "IntermediateField AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve"
open scoped MatrixGroups ModularForm Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm IsIntegralQExp isIntegralQExp_iff intSeriesC qExpFunctionFieldC div_mem_qExpFunctionFieldC x1FunctionField x1FunctionFieldBar JOne eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange IsBaseChangeAutOf baseChangeAut isBaseChangeAutOf_baseChangeAut baseChangeAut_of_not slashQExpC IsDiamondAut diamondAut isDiamondAut_diamondAut diamondAut_of_not diamondAutBar diamondOneBar diamondOneBar_apply translation_mem_GammaH GammaH_bot jqModC map_jqModC jqModC_mem IsLaurentPlaceReduction laurentIntegralPrincipalDivisors LaurentPrincipalGeneratedByIntegral LaurentReductionInputs laurentReductionDegZero coe_laurentReductionDegZero laurentReduction laurentReduction_mk IsLaurentPlaceReduction.eq_or_const_of_agree ReductionInputsQExpModL reductionQExpModL reductionQExpModL_of_not qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit transcendental_jqModC finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField exists_constantReduction_pic0Map_eq_reductionQExpModL exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace DiaRed
p2m_open "ModularCurve"

section ReducedAut

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  (R : RegularProlongation A F Fbar) (σ : F ≃ₐ[L] F)
  (hσ : ∀ f : F, σ f ∈ R.integers ↔ f ∈ R.integers)

include hσ in

theorem symm_mem_iff (f : F) : σ.symm f ∈ R.integers ↔ f ∈ R.integers := by
  have h := hσ (σ.symm f)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

def restrictInt : R.integers ≃+* R.integers where
  toFun f := ⟨σ f, (hσ f).mpr f.2⟩
  invFun f := ⟨σ.symm f, (symm_mem_iff R σ hσ f).mpr f.2⟩
  left_inv f := Subtype.ext (σ.symm_apply_apply _)
  right_inv f := Subtype.ext (σ.apply_symm_apply _)
  map_mul' f g := Subtype.ext (map_mul σ _ _)
  map_add' f g := Subtype.ext (map_add σ _ _)

@[scoped simp] theorem coe_restrictInt (f : R.integers) : ((restrictInt R σ hσ f : R.integers) : F) = σ f := rfl

theorem ker_residue_le :
    RingHom.ker R.residue ≤ RingHom.ker (R.residue.comp (restrictInt R σ hσ).toRingHom) := by
  intro f hf
  rw [RingHom.mem_ker, RingHom.comp_apply]
  change R.residue (restrictInt R σ hσ f) = 0
  have hf' : restrictInt R σ hσ f ∈ RingHom.ker R.residue := by
    rw [R.ker_residue, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
    intro hu
    apply hf
    have := hu.map (restrictInt R σ hσ).symm
    rwa [RingEquiv.symm_apply_apply] at this
  exact hf'

def redHom : Fbar →+* Fbar :=
  (R.residue.liftOfRightInverse (Function.surjInv R.residue_surjective)
    (Function.rightInverse_surjInv R.residue_surjective))
    ⟨R.residue.comp (restrictInt R σ hσ).toRingHom, ker_residue_le R σ hσ⟩

theorem redHom_residue (f : R.integers) :
    redHom R σ hσ (R.residue f) = R.residue ⟨σ f, (hσ f).mpr f.2⟩ :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ f

theorem redHom_symm_comp :
    (redHom R σ.symm (symm_mem_iff R σ hσ)).comp (redHom R σ hσ) = RingHom.id Fbar := by
  refine RingHom.ext fun x => ?_
  obtain ⟨f, rfl⟩ := R.residue_surjective x
  rw [RingHom.comp_apply, redHom_residue, redHom_residue, RingHom.id_apply]
  congr 1
  exact Subtype.ext (σ.symm_apply_apply _)

theorem redHom_comp_symm :
    (redHom R σ hσ).comp (redHom R σ.symm (symm_mem_iff R σ hσ)) = RingHom.id Fbar := by
  refine RingHom.ext fun x => ?_
  obtain ⟨f, rfl⟩ := R.residue_surjective x
  rw [RingHom.comp_apply, redHom_residue, redHom_residue, RingHom.id_apply]
  congr 1
  exact Subtype.ext (σ.apply_symm_apply _)

def redAut : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (redHom R σ hσ) (redHom R σ.symm (symm_mem_iff R σ hσ))
      (redHom_comp_symm R σ hσ) (redHom_symm_comp R σ hσ))
    (fun c => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      change redHom R σ hσ _ = _
      rw [← R.residue_algebraMap a, redHom_residue]
      congr 1
      exact Subtype.ext (σ.commutes (a : L)))

theorem redAut_residue (f : R.integers) :
    redAut R σ hσ (R.residue f) = R.residue ⟨σ f, (hσ f).mpr f.2⟩ :=
  redHom_residue R σ hσ f

theorem residue_apply_eq (f : F) (hf : f ∈ R.integers) :
    R.residue ⟨σ f, (hσ f).mpr hf⟩ = redAut R σ hσ (R.residue ⟨f, hf⟩) :=
  (redAut_residue R σ hσ ⟨f, hf⟩).symm

end ReducedAut

section Rigidity

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
variable {Fbar : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))}

local notation "FL" => laurentBaseChange L F₀
local notation "kA" => IsLocalRing.ResidueField A

theorem mapDomain_eq_zero_of_const {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K']
    [Field F'] [Algebra K' F'] {r : Place K F → Place K' F'} (hconst : ∀ P Q, r P = r Q)
    (hdeg : ∀ P : Place K F, P.deg = 1) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Finsupp.mapDomain r D = 0 := by
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨P₀⟩⟩
  · have : D = 0 := Finsupp.ext fun P => isEmptyElim P
    rw [this, Finsupp.mapDomain_zero]
  · have hmapconst : ∀ D : Divisor K F,
        Finsupp.mapDomain r D = Finsupp.single (r P₀) (Divisor.degree D) := by
      intro D
      induction D using Finsupp.induction with
      | zero => simp
      | single_add P n D _ _ ih =>
        rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hconst P P₀, map_add,
          Divisor.degree_single, hdeg, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
    rw [hmapconst D, (Divisor.mem_degZero.mp hD), Finsupp.single_zero]

theorem smul_divisor_apply_eq_ord {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) {f : F} {D : Divisor K F} (hD : ∀ P, D P = P.ord f) (P : Place K F) :
    (g • D) P = P.ord (g • f) := by
  rw [SemilinearAut.divisor_smul_apply, hD, ← SemilinearAut.ord_smul g (g⁻¹ • P), smul_inv_smul]

theorem mapDomain_agree
    (h : LaurentReductionInputs A (IsLocalRing.residue A) F₀ Fbar)
    (R : ConstantReduction A FL Fbar) (hR : R.placeMap = h.choose)
    (hres : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FL)
      (hyk : coeffMap (IsLocalRing.residue A) y ∈ Fbar),
      ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FL) ∈ R.integers,
        R.residue ⟨_, hO⟩ = ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩)
    (σ : FL ≃ₐ[L] FL) (hσ : ∀ f : FL, σ f ∈ R.integers ↔ f ∈ R.integers)
    (δ : Fbar ≃ₐ[kA] Fbar)
    (hδ : ∀ (f : FL) (hf : f ∈ R.integers), R.residue ⟨σ f, (hσ f).mpr hf⟩ = δ (R.residue ⟨f, hf⟩))
    {D : Divisor L FL}
    (hD : D ∈ laurentIntegralPrincipalDivisors A (IsLocalRing.residue A) F₀ Fbar) :
    Finsupp.mapDomain h.choose D =
      Finsupp.mapDomain ((fun Q => (SemilinearAut.ofAlgAut δ)⁻¹ • Q) ∘ h.choose ∘
        fun P => SemilinearAut.ofAlgAut σ • P) D := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  set gσ := SemilinearAut.ofAlgAut σ with hgσ
  set gδ := SemilinearAut.ofAlgAut δ with hgδ
  set x : FL := ⟨coeffMap A.subtype y, hy⟩ with hx
  set ybar : Fbar := ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ with hybar
  have hybar0 : ybar ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
  obtain ⟨hxO, hxres⟩ := hres y hy hyk

  have hσxO : σ x ∈ R.integers := (hσ x).mpr hxO
  have hσxres : R.residue ⟨σ x, hσxO⟩ = δ ybar := by rw [hδ x hxO, hxres]
  have hσxne : R.residue ⟨σ x, hσxO⟩ ≠ 0 := by
    rw [hσxres]; exact (map_ne_zero δ).mpr hybar0

  have hD' : ∀ P, (gσ • D) P = P.ord (σ x) := fun P => smul_divisor_apply_eq_ord gσ hDy P

  rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def,
    ← SemilinearAut.divisor_smul_def]
  ext Q

  rw [h.choose_spec.1.2 y hy hyk hne D hDy Q]

  rw [SemilinearAut.divisor_smul_apply, inv_inv, ← hR,
    R.mapDomain_placeMap ⟨σ x, hσxO⟩ hσxne (gσ • D) hD' (gδ • Q), hσxres,
    show (δ ybar : Fbar) = gδ • ybar from rfl, SemilinearAut.ord_smul]

theorem laurentReduction_smul
    (h : LaurentReductionInputs A (IsLocalRing.residue A) F₀ Fbar)
    (R : ConstantReduction A FL Fbar) (hR : R.placeMap = h.choose)
    (hres : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FL)
      (hyk : coeffMap (IsLocalRing.residue A) y ∈ Fbar),
      ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FL) ∈ R.integers,
        R.residue ⟨_, hO⟩ = ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩)
    (σ : FL ≃ₐ[L] FL) (hσ : ∀ f : FL, σ f ∈ R.integers ↔ f ∈ R.integers)
    (δ : Fbar ≃ₐ[kA] Fbar)
    (hδ : ∀ (f : FL) (hf : f ∈ R.integers), R.residue ⟨σ f, (hσ f).mpr hf⟩ = δ (R.residue ⟨f, hf⟩))
    (hdegL : ∀ P : Place L FL, P.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L FL, ∃ y : Pic0 L FL, n • y = x)
    (x : Pic0 L FL) :
    laurentReduction A (IsLocalRing.residue A) F₀ Fbar (SemilinearAut.ofAlgAut σ • x) =
      SemilinearAut.ofAlgAut δ • laurentReduction A (IsLocalRing.residue A) F₀ Fbar x := by
  set r := h.choose with hrdef
  have hr : IsLaurentPlaceReduction A (IsLocalRing.residue A) F₀ Fbar r := h.choose_spec.1
  have hgen : LaurentPrincipalGeneratedByIntegral A (IsLocalRing.residue A) F₀ Fbar := h.choose_spec.2
  set gσ := SemilinearAut.ofAlgAut σ with hgσ
  set gδ := SemilinearAut.ofAlgAut δ with hgδ
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, laurentReduction_mk h, laurentReduction_mk h, SemilinearAut.pic0_smul_mk]
  rcases IsLaurentPlaceReduction.eq_or_const_of_agree (r₁ := r)
      (r₂ := (fun Q => gδ⁻¹ • Q) ∘ r ∘ fun P => gσ • P) hgen
      (fun D hD => mapDomain_agree h R hR hres σ hσ δ hδ hD) hdegL hdiv with key | hconst
  · have hfun : (r ∘ fun P => gσ • P) = (fun Q => gδ • Q) ∘ r := by
      funext P
      have hP := congrFun key P
      simp only [Function.comp_apply] at hP ⊢
      rw [hP, smul_inv_smul]
    congr 1
    apply Subtype.ext
    rw [coe_laurentReductionDegZero, SemilinearAut.coe_degZeroSMulHom, SemilinearAut.coe_degZeroSMulHom,
      coe_laurentReductionDegZero, SemilinearAut.divisor_smul_def gσ, ← Finsupp.mapDomain_comp,
      SemilinearAut.divisor_smul_def gδ, ← Finsupp.mapDomain_comp]
    exact congrArg (fun φ => Finsupp.mapDomain φ (D : Divisor L FL)) hfun
  ·
    have h0 : ∀ E : Divisor.degZero (K := L) (F := FL),
        laurentReductionDegZero h.choose h.choose_spec.1.1 E = 0 := fun E =>
      Subtype.ext (by rw [coe_laurentReductionDegZero]; exact mapDomain_eq_zero_of_const hconst hdegL E.2)
    rw [h0, h0, Pic0.mk_zero, ← SemilinearAut.pic0_smul_mk]
    exact (smul_zero (A := Pic0 kA Fbar) gδ).symm

end Rigidity

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem coeffMap_intSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : PowerSeries ℤ) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R (p.map (Int.castRingHom R))) =
      HahnSeries.ofPowerSeries ℤ S (p.map (Int.castRingHom S)) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffEmb_intSeriesC [Algebra ℚ L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p :=
  coeffMap_intSeries _ p

theorem coeffMap_ratComplex_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ)) :=
  coeffMap_intSeries _ p

end Coeff

section Forms

open ModularForm UpperHalfPlane EisensteinSeries

def δZ : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

def e4cube1 : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

theorem qExpansion_e4cube1 : qExpansion 1 (e4cube1) = (eisenstein4 ^ 3).map (Int.castRingHom ℂ) := by
  rw [e4cube1, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    map_pow, isIntegralQExp_E4]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) e4cube1

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem coe_e4cube : (e4cube Γ : ℍ → ℂ) = e4cube1 := rfl

theorem isIntegralQExp_e4cube : IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, coe_e4cube, qExpansion_e4cube1]

theorem isIntegralQExp_delta : IsIntegralQExp (delta Γ : ℍ → ℂ) δZ :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem slash_e4cube (γ : SL(2, ℤ)) :
    (e4cube Γ : ℍ → ℂ) ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ) = e4cube Γ := by
  rw [coe_e4cube]
  exact SlashInvariantForm.slash_action_eqn e4cube1 _ ⟨γ, rfl⟩

theorem slash_delta (γ : SL(2, ℤ)) :
    (delta Γ : ℍ → ℂ) ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ) = delta Γ :=
  SlashInvariantForm.slash_action_eqn (CuspForm.discriminant : ModularForm 𝒮ℒ 12) _ ⟨γ, rfl⟩

theorem intSeriesC_delta_ne_zero (K : Type*) [Field K] : intSeriesC K δZ ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  have h2 : (HahnSeries.ofPowerSeries ℤ K (δZ.map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, δZ,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem jqModC_mul_delta (K : Type*) [Field K] :
    jqModC K * intSeriesC K δZ = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, δZ, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_div (K : Type*) [Field K] :
    jqModC K = intSeriesC K (eisenstein4 ^ 3) / intSeriesC K δZ := by
  rw [eq_div_iff (intSeriesC_delta_ne_zero K), jqModC_mul_delta]

theorem jqModC_mem (K : Type*) [Field K] : jqModC K ∈ qExpFunctionFieldC K Γ := by
  rw [jqModC_eq_div]
  exact div_mem_qExpFunctionFieldC (e4cube Γ) (delta Γ) (isIntegralQExp_e4cube Γ) (isIntegralQExp_delta Γ)
    (intSeriesC_delta_ne_zero K)

end Forms

section DiamondJ

open ModularForm UpperHalfPlane

variable (M : ℕ) [NeZero M]

local notation "Qb" => AlgebraicClosure ℚ

theorem exists_gamma0_apply_eq {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨u, v, huv⟩ : IsCoprime (d : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hd
  refine ⟨⟨!![(d : ℤ), -v; (M : ℤ), u], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  · show (((d : ℤ)) : ZMod M) = (d : ZMod M)
    rw [Int.cast_natCast]

theorem diamondAut_apply_j (d : ℕ) (hjQ : jqModC ℚ ∈ x1FunctionField M) :
    diamondAut M d ⟨jqModC ℚ, hjQ⟩ = ⟨jqModC ℚ, hjQ⟩ := by
  classical
  by_cases hex : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ
  · obtain ⟨hcop, hprop⟩ := isDiamondAut_diamondAut hex
    obtain ⟨γ, hγ0, hγd⟩ := exists_gamma0_apply_eq M hcop
    have hΓ : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) =
        (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) := rfl
    have h := hprop 12 (e4cube (CongruenceSubgroup.Gamma1 M)) (delta (CongruenceSubgroup.Gamma1 M))
      (eisenstein4 ^ 3) δZ (isIntegralQExp_e4cube _) (isIntegralQExp_delta _) (intSeriesC_delta_ne_zero ℚ)
      γ hγ0 hγd

    have hsD : slashQExpC 12 (delta (CongruenceSubgroup.Gamma1 M) : ℍ → ℂ) γ =
        coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ δZ) := by
      rw [slashQExpC, slash_delta, ← isIntegralQExp_delta (CongruenceSubgroup.Gamma1 M),
        coeffMap_ratComplex_intSeriesC]
    have hsE : slashQExpC 12 (e4cube (CongruenceSubgroup.Gamma1 M) : ℍ → ℂ) γ =
        coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ (eisenstein4 ^ 3)) := by
      rw [slashQExpC, slash_e4cube, ← isIntegralQExp_e4cube (CongruenceSubgroup.Gamma1 M),
        coeffMap_ratComplex_intSeriesC]
    rw [hsD, hsE, ← map_mul] at h
    have hinj : Function.Injective (coeffMap (algebraMap ℚ ℂ) : LaurentSeries ℚ → LaurentSeries ℂ) :=
      (coeffMap (algebraMap ℚ ℂ)).injective
    have h2 := hinj h
    have helt : (⟨jqModC ℚ, hjQ⟩ : x1FunctionField M) =
        ⟨intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ δZ,
          div_mem_qExpFunctionFieldC (e4cube _) (delta _) (isIntegralQExp_e4cube _) (isIntegralQExp_delta _)
            (intSeriesC_delta_ne_zero ℚ)⟩ := Subtype.ext (jqModC_eq_div ℚ)
    rw [helt]
    apply Subtype.ext
    change _ = intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ δZ
    rw [eq_div_iff (intSeriesC_delta_ne_zero ℚ)]
    exact h2
  · rw [diamondAut_of_not hex]
    rfl

theorem diamondAutBar_apply_j (d : ℕ) (hjF : coeffEmb Qb (jqModC ℚ) ∈ x1FunctionFieldBar M) :
    diamondAutBar M d ⟨coeffEmb Qb (jqModC ℚ), hjF⟩ = ⟨coeffEmb Qb (jqModC ℚ), hjF⟩ := by
  classical
  have hjQ : jqModC ℚ ∈ x1FunctionField M := jqModC_mem (CongruenceSubgroup.Gamma1 M) ℚ
  unfold diamondAutBar
  by_cases hex : ∃ σ : x1FunctionFieldBar M ≃ₐ[Qb] x1FunctionFieldBar M,
      IsBaseChangeAutOf Qb (diamondAut M d) σ
  · have hb := isBaseChangeAutOf_baseChangeAut hex ⟨jqModC ℚ, hjQ⟩
    rw [diamondAut_apply_j M d hjQ] at hb
    exact Subtype.ext hb
  · rw [baseChangeAut_of_not hex]
    rfl

end DiamondJ

section GaussInvariance

variable (M : ℕ) [NeZero M] {p : ℕ} [Fact p.Prime] (hpM : ¬ p ∣ M)
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)

local notation "Qb" => AlgebraicClosure ℚ
local notation "Γ₁" => CongruenceSubgroup.Gamma1 M
local notation "F1" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
local notation "kP" => IsLocalRing.ResidueField P
local notation "Fb1" => qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)

theorem T_mem_Gamma1 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [← GammaH_bot M]; exact translation_mem_GammaH M ⊥

def fixedIF {L E : Type*} [Field L] [Field E] [Algebra L E] (τ : E ≃ₐ[L] E) : IntermediateField L E where
  carrier := {e | τ e = e}
  mul_mem' {a b} ha hb := by
    change τ (a * b) = a * b
    rw [map_mul, show τ a = a from ha, show τ b = b from hb]
  one_mem' := map_one τ
  add_mem' {a b} ha hb := by
    change τ (a + b) = a + b
    rw [map_add, show τ a = a from ha, show τ b = b from hb]
  zero_mem' := map_zero τ
  algebraMap_mem' r := τ.commutes r
  inv_mem' a ha := by
    change τ a⁻¹ = a⁻¹
    rw [map_inv₀, show τ a = a from ha]

theorem apply_eq_self_of_mem_adjoin {L E : Type*} [Field L] [Field E] [Algebra L E] (τ : E ≃ₐ[L] E)
    {x : E} (hx : τ x = x) {e : E} (he : e ∈ IntermediateField.adjoin L ({x} : Set E)) : τ e = e := by
  have hle : IntermediateField.adjoin L ({x} : Set E) ≤ fixedIF τ :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact hle he

include hpM hP in

theorem finrank_le_gamma1 (x : Fb1) (y : F1) (hx : (x : LaurentSeries kP) = jqModC kP)
    (hy : (y : LaurentSeries Qb) = jqModC Qb) :
    Module.finrank (IntermediateField.adjoin Qb ({y} : Set F1)) F1 ≤
      Module.finrank (IntermediateField.adjoin kP ({x} : Set Fb1)) Fb1 := by
  have h := ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M ⊥ hpM P hP
  rw [GammaH_bot] at h
  exact h x y hx hy

include hpM hP in

theorem apply_mem_integers_iff (R : RegularProlongation P F1 Fb1) (x₀ : R.integers)
    (hx₀ : ((x₀ : F1) : LaurentSeries Qb) = jqModC Qb)
    (hres₀ : ((R.residue x₀ : Fb1) : LaurentSeries kP) = jqModC kP)
    (σ : F1 ≃ₐ[Qb] F1) (hσj : σ (x₀ : F1) = x₀) :
    ∀ f : F1, σ f ∈ R.integers ↔ f ∈ R.integers := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance

  obtain ⟨xP, hxP, htrP, hfinP, hleP⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField Qb P Γ₁ (T_mem_Gamma1 M)
  obtain rfl : xP = R.residue x₀ := Subtype.ext (hxP.trans hres₀.symm)
  haveI := hfinP
  have hpos : 0 < Module.finrank (IntermediateField.adjoin kP ({R.residue x₀} : Set Fb1)) Fb1 :=
    Module.finrank_pos
  have hle1 := hleP (x₀ : F1) hx₀
  have hle2 := finrank_le_gamma1 M hpM P hP (R.residue x₀) (x₀ : F1) hres₀ hx₀
  have hdeg := le_antisymm hle2 hle1

  set V : ValuationSubring F1 := R.integers.comap (σ : F1 →+* F1) with hV
  have hVmem : ∀ e, e ∈ V ↔ σ e ∈ R.integers := fun e => ValuationSubring.mem_comap
  have hVeq : V = R.integers := by
    refine AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff P R x₀ ?_ hpos hdeg V ?_
    · intro halg
      apply ModularCurve.transcendental_jqModC kP
      have := halg.algebraMap (A := LaurentSeries kP)
      rwa [show algebraMap Fb1 (LaurentSeries kP) (R.residue x₀) = jqModC kP from hres₀] at this
    · intro e he
      rw [hVmem, apply_eq_self_of_mem_adjoin σ hσj he]
  intro f
  rw [← hVmem, hVeq]

end GaussInvariance

section Assembly

variable (M : ℕ) [NeZero M] {p : ℕ} [Fact p.Prime] (hpM : ¬ p ∣ M)
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) (d : ℕ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "Γ₁" => CongruenceSubgroup.Gamma1 M
local notation "F1" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
local notation "kP" => IsLocalRing.ResidueField P
local notation "Fb1" => qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)

theorem jhat_mem : coeffEmb Qb (jqModC ℚ) ∈ F1 :=
  coeffEmb_mem_laurentBaseChange _ (jqModC_mem Γ₁ ℚ)

theorem ι_jqModC : ι P (jqModC P) = coeffEmb Qb (jqModC ℚ) := by
  change (jqModC P).map _ = (jqModC ℚ).map _
  rw [map_jqModC, map_jqModC]

theorem ι_jqModC_mem : ι P (jqModC P) ∈ F1 := by
  rw [ι_jqModC]; exact jhat_mem M

theorem ϖ_jqModC : ϖ P (jqModC P) = jqModC kP := map_jqModC _

theorem ϖ_jqModC_mem : ϖ P (jqModC P) ∈ Fb1 := by
  rw [ϖ_jqModC]; exact jqModC_mem Γ₁ kP

include hpM hP in

theorem exists_hσ_and_pinning (R : RegularProlongation P F1 Fb1)
    (hres : ∀ (y : LaurentSeries P) (hy : ι P y ∈ F1) (hyk : ϖ P y ∈ Fb1),
      ∃ hO : (⟨ι P y, hy⟩ : F1) ∈ R.integers, R.residue ⟨_, hO⟩ = ⟨ϖ P y, hyk⟩)
    (σ : F1 ≃ₐ[Qb] F1) (hσdef : ∀ f : F1, σ f = diamondAutBar M d f) :
    ∃ hσ : (∀ f : F1, σ f ∈ R.integers ↔ f ∈ R.integers),
      ∀ (y y' : LaurentSeries P) (hy : ι P y ∈ F1) (hy' : ι P y' ∈ F1) (hyk : ϖ P y ∈ Fb1)
        (hyk' : ϖ P y' ∈ Fb1), σ ⟨ι P y, hy⟩ = ⟨ι P y', hy'⟩ →
          redAut R σ hσ ⟨ϖ P y, hyk⟩ = ⟨ϖ P y', hyk'⟩ := by

  obtain ⟨hjO, hjres⟩ := hres (jqModC P) (ι_jqModC_mem M P) (ϖ_jqModC_mem M P)
  set x₀ : R.integers := ⟨⟨ι P (jqModC P), ι_jqModC_mem M P⟩, hjO⟩ with hx₀
  have hx₀coe : ((x₀ : F1) : LaurentSeries Qb) = jqModC Qb := by
    change ι P (jqModC P) = _
    change (jqModC P).map _ = _
    exact map_jqModC _
  have hres₀ : ((R.residue x₀ : Fb1) : LaurentSeries kP) = jqModC kP := by
    rw [hx₀, hjres]
    exact ϖ_jqModC P

  have hσj : σ (x₀ : F1) = x₀ := by
    have hxeq : (x₀ : F1) = ⟨coeffEmb Qb (jqModC ℚ), jhat_mem M⟩ := Subtype.ext (ι_jqModC P)
    rw [hσdef, hxeq]
    exact diamondAutBar_apply_j M d (jhat_mem M)
  have hσ : ∀ f : F1, σ f ∈ R.integers ↔ f ∈ R.integers :=
    apply_mem_integers_iff M hpM P hP R x₀ hx₀coe hres₀ σ hσj
  refine ⟨hσ, fun y y' hy hy' hyk hyk' hyy' => ?_⟩
  obtain ⟨hyO, hyres⟩ := hres y hy hyk
  obtain ⟨hyO', hyres'⟩ := hres y' hy' hyk'
  rw [← hyres, redAut_residue, ← hyres']
  congr 1
  exact Subtype.ext hyy'

include hpM hP in

theorem main :
    ∃ δ : Fb1 ≃ₐ[kP] Fb1,
      (∀ (y y' : LaurentSeries P) (hy : ι P y ∈ F1) (hy' : ι P y' ∈ F1) (hyk : ϖ P y ∈ Fb1)
          (hyk' : ϖ P y' ∈ Fb1),
          diamondAutBar M d (⟨ι P y, hy⟩ : F1) = ⟨ι P y', hy'⟩ → δ ⟨ϖ P y, hyk⟩ = ⟨ϖ P y', hyk'⟩) ∧
      ∀ z : Pic0 Qb F1,
        reductionQExpModL P Γ₁ (SemilinearAut.ofAlgAut (K := Qb) (F := F1) (diamondAutBar M d) • z) =
          SemilinearAut.ofAlgAut δ • reductionQExpModL P Γ₁ z := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  have hT : ModularGroup.T ∈ Γ₁ := T_mem_Gamma1 M

  let σ : F1 ≃ₐ[Qb] F1 := diamondAutBar M d
  have hσdef : ∀ f : F1, σ f = diamondAutBar M d f := fun f => rfl
  by_cases hin : ReductionInputsQExpModL P Γ₁
  ·
    obtain ⟨R, hRr, -, hres⟩ :=
      ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL Γ₁ hT P hin
    obtain ⟨hσ, hpin⟩ := exists_hσ_and_pinning M hpM P hP d R.toRegularProlongation hres σ hσdef
    set δ := redAut R.toRegularProlongation σ hσ with hδdef
    have hδ : ∀ (f : F1) (hf : f ∈ R.integers), R.residue ⟨σ f, (hσ f).mpr hf⟩ = δ (R.residue ⟨f, hf⟩) :=
      fun f hf => residue_apply_eq R.toRegularProlongation σ hσ f hf

    obtain ⟨t, ht, hfd⟩ :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qb Γ₁ hT
    haveI : IsCurveOver Qb F1 := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht hfd
    have hdegL : ∀ Q : Place Qb F1, Q.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
    have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 Qb F1, ∃ y : Pic0 Qb F1, n • y = x :=
      fun n hn x => AlgebraicCurve.Pic0.exists_nsmul_eq Qb F1 ⟨t, ht, hfd⟩ n hn x
    refine ⟨δ, fun y y' hy hy' hyk hyk' hyy' => hpin y y' hy hy' hyk hyk' hyy', fun z => ?_⟩
    have hRr' : R.placeMap = hin.choose := hRr
    exact laurentReduction_smul hin R hRr' hres σ hσ δ hδ hdegL hdiv z
  ·
    obtain ⟨R, -, hRres⟩ :=
      ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC Qb P Γ₁ hT
    have hres : ∀ (y : LaurentSeries P) (hy : ι P y ∈ F1) (hyk : ϖ P y ∈ Fb1),
        ∃ hO : (⟨ι P y, hy⟩ : F1) ∈ R.integers, R.residue ⟨_, hO⟩ = ⟨ϖ P y, hyk⟩ := by
      intro y hy hyk
      obtain ⟨hO, hval⟩ := hRres y hy
      exact ⟨hO, Subtype.ext hval⟩
    obtain ⟨hσ, hpin⟩ := exists_hσ_and_pinning M hpM P hP d R hres σ hσdef
    refine ⟨redAut R σ hσ, fun y y' hy hy' hyk hyk' hyy' => hpin y y' hy hy' hyk hyk' hyy', fun z => ?_⟩
    rw [reductionQExpModL_of_not hin, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
    exact (smul_zero (A := Pic0 kP Fb1) (SemilinearAut.ofAlgAut (redAut R σ hσ))).symm

end Assembly

end ModularCurve.DiaRed
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve.DiaRed"
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve.DiaRed"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul.ModularCurve ModularCurve.DiaRed in
set_option maxHeartbeats 16000000 in
theorem solution (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) (d : ℕ) :
    ∃ δ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)
        ≃ₐ[IsLocalRing.ResidueField P]
        ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M),
      (∀ (y y' : LaurentSeries P)
          (hy : ModularCurve.coeffMap P.subtype y ∈ ModularCurve.x1FunctionFieldBar M)
          (hy' : ModularCurve.coeffMap P.subtype y' ∈ ModularCurve.x1FunctionFieldBar M)
          (hyk : ModularCurve.coeffMap (IsLocalRing.residue P) y ∈
            ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M))
          (hyk' : ModularCurve.coeffMap (IsLocalRing.residue P) y' ∈
            ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)),
          ModularCurve.diamondAutBar M d
              (⟨ModularCurve.coeffMap P.subtype y, hy⟩ : ModularCurve.x1FunctionFieldBar M) =
              ⟨ModularCurve.coeffMap P.subtype y', hy'⟩ →
            δ ⟨ModularCurve.coeffMap (IsLocalRing.residue P) y, hyk⟩ =
              ⟨ModularCurve.coeffMap (IsLocalRing.residue P) y', hyk'⟩) ∧
      ∀ z : ModularCurve.JOne M,
        ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M) (ModularCurve.diamondOneBar M d z) =
          AlgebraicCurve.SemilinearAut.ofAlgAut δ •
            ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M) z := by
  obtain ⟨δ, hpin, hred⟩ := ModularCurve.DiaRed.main M hpM P hP d
  refine ⟨δ, fun y y' hy hy' hyk hyk' h => hpin y y' hy hy' hyk hyk' h, fun z => ?_⟩
  rw [ModularCurve.diamondOneBar_apply]
  exact hred z

end S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_reductionQExpModL_gamma1_diamondOneBar_eq_smul (solution)
