-- Prove2me | solution 1 for ModularCurve.XOneP.exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/14863944-f031-554b-8fe6-84418f5e6c5e

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_chartMap_finite_of_algHom
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaOneBar_of_neZero
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
import Theorems.Thm_AlgebraicGeometry_exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaOneBar
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper"
p2m_attr_erase "simp" "CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace H5Aux

theorem morphismRestrict_of_le {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens} (hWV : W ≤ V) (hf : P (f ∣_ V)) : P (f ∣_ W) := by
  have h1 : P (f ∣_ V ∣_ (V.ι ⁻¹ᵁ W)) := IsZariskiLocalAtTarget.restrict hf _
  have h2 : P (f ∣_ (V.ι ''ᵁ (V.ι ⁻¹ᵁ W))) := (P.arrow_mk_iso_iff (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ W))).mp h1
  have hW : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]
  exact (P.arrow_mk_iso_iff (morphismRestrictEq f hW)).mp h2

theorem flat_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens} (hWV : W ≤ V)
    [hf : Flat (f ∣_ V)] : Flat (f ∣_ W) :=
  morphismRestrict_of_le (P := @Flat) f hWV hf

theorem locallyOfFinitePresentation_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens}
    (hWV : W ≤ V) [hf : LocallyOfFinitePresentation (f ∣_ V)] : LocallyOfFinitePresentation (f ∣_ W) :=
  morphismRestrict_of_le (P := @LocallyOfFinitePresentation) f hWV hf

theorem finrank_morphismRestrict_eq_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {V W : Y.Opens} (hWV : W ≤ V)
    [Flat (f ∣_ V)] (y : Y) (hyW : y ∈ W) :
    haveI : Flat (f ∣_ W) := flat_morphismRestrict_of_le f hWV
    (f ∣_ W).finrank ⟨y, hyW⟩ = (f ∣_ V).finrank ⟨y, hWV hyW⟩ := by
  haveI : Flat (f ∣_ W) := flat_morphismRestrict_of_le f hWV
  rw [AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank f W y hyW,
    AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank f V y (hWV hyW)]

end H5Aux

namespace H5Aux

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) := by
  ext k
  rw [ModularCurve.coeffEmb_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffEmb_coeff]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd n _ hk, ModularCurve.qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem o1_changeOfGenerator_inputs
    (p M : ℕ) (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (j' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hj' : ((j' : LaurentSeries L)) = ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq)) [Fact (j' ≠ 0)] :
    j' ∈ TwoChartIntegralModel.chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ ∧
    jℓ ∈ TwoChartIntegralModel.chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j' ∧
    (∀ y ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j',
      ∃ s ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ,
        (∃ a ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ, s = 1 + jℓ⁻¹ * a) ∧
        s * y ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ) ∧
    (∀ y ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ,
      ∃ s ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j',
        (∃ a ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j', s = 1 + j'⁻¹ * a) ∧
        s * y ∈ TwoChartIntegralModel.chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j') := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hj'2 : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ ℓ ModularCurve.jq) := by
    rw [hj', coeffEmb_qExpand]
  exact ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand ℓ L
    (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) A jℓ hjℓ j' hj'2

end H5Aux

namespace H5Aux

theorem finite_toRingHom_heckeAlphaOneBar (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] :
    (ModularCurve.heckeAlphaOneBar L N ℓ).toRingHom.Finite :=
  ModularCurve.finiteAlong_heckeAlphaOneBar_of_neZero L N ℓ

theorem finite_toRingHom_heckeBetaOneBar (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ]
    (h : ModularCurve.HeckeBetaOneDefined N ℓ) :
    (ModularCurve.heckeBetaOneBar L N ℓ).toRingHom.Finite :=
  ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined L N ℓ h

theorem finite_of_coe_eq {F F' : Type*} [CommRing F] [CommRing F'] (φ ψ : F →+* F') (h : ⇑φ = ⇑ψ) (hφ : φ.Finite) :
    ψ.Finite := by
  obtain rfl : φ = ψ := RingHom.ext (congrFun h)
  exact hφ

end H5Aux

namespace H5Aux

theorem exists_ringEquiv_functionField_of_isOpenImmersion' {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f] :
    ∃ e : X.functionField ≃+* Y.functionField,
      Y.fromSpecStalk (genericPoint Y) ≫ f = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X) := by
  have hgen : f (genericPoint Y) = genericPoint X := genericPoint_eq_of_isOpenImmersion f
  have hins : Inseparable (genericPoint X) (f (genericPoint Y)) := Inseparable.of_eq hgen.symm
  let θ : X.functionField ≅ Y.functionField := X.presheaf.stalkCongr hins ≪≫ asIso (f.stalkMap (genericPoint Y))
  refine ⟨θ.commRingCatIsoToRingEquiv, ?_⟩
  have hθ : CommRingCat.ofHom θ.commRingCatIsoToRingEquiv.toRingHom =
      X.presheaf.stalkSpecializes hins.ge ≫ f.stalkMap (genericPoint Y) := rfl
  rw [hθ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem exists_ringEquiv_functionField_of_isFractionRing {X : Scheme.{u}} [IsIntegral X]
    (C : CommRingCat.{u}) [IsDomain C] (ι : Spec C ⟶ X) [IsOpenImmersion ι]
    (F : Type u) [Field F] [Algebra C F] [IsFractionRing C F] :
    ∃ eF : F ≃+* X.functionField,
      Spec.map (CommRingCat.ofHom eF.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap C F)) ≫ ι =
        X.fromSpecStalk (genericPoint X) := by
  haveI : IsIntegral (Spec C) := inferInstance
  obtain ⟨e₁, he₁⟩ := exists_ringEquiv_functionField_of_isOpenImmersion' ι
  let e₂ : F ≃ₐ[C] (Spec C).functionField := IsLocalization.algEquiv (nonZeroDivisors C) F (Spec C).functionField
  refine ⟨e₂.toRingEquiv.trans e₁.symm, ?_⟩
  have hcomp : (e₂.toRingEquiv.trans e₁.symm).toRingHom.comp (algebraMap C F) =
      e₁.symm.toRingHom.comp (algebraMap C (Spec C).functionField) := by
    ext x
    show e₁.symm (e₂ (algebraMap C F x)) = e₁.symm (algebraMap C (Spec C).functionField x)
    rw [e₂.commutes]
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap C (Spec C).functionField)) = (Spec C).fromSpecStalk (genericPoint (Spec C)) :=
    (Spec.fromSpecStalk_eq' C (genericPoint (Spec C))).symm
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hcomp, CommRingCat.ofHom_comp, Spec.map_comp_assoc, h2, he₁,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hid : e₁.symm.toRingHom.comp e₁.toRingHom = RingHom.id _ := by ext x; exact e₁.symm_apply_apply x
  rw [hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

theorem exists_ringEquiv_functionField_twoChartIntegralModel
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (hFrac : IsFractionRing ↥(TwoChartIntegralModel.chartAlgFin R F j) F) :
    haveI := AlgebraicCurve.TwoChartIntegralModel.isIntegral R F j
    ∃ eF : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField,
      Spec.map (CommRingCat.ofHom eF.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) F)) ≫
            TwoChartIntegralModel.ιFin R F j =
        (AlgebraicCurve.TwoChartIntegralModel R F j).fromSpecStalk (genericPoint _) := by
  haveI := AlgebraicCurve.TwoChartIntegralModel.isIntegral R F j
  haveI : IsDomain (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j)) :=
    inferInstanceAs (IsDomain ↥(TwoChartIntegralModel.chartAlgFin R F j))
  letI : Algebra (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j)) F :=
    inferInstanceAs (Algebra ↥(TwoChartIntegralModel.chartAlgFin R F j) F)
  haveI : IsFractionRing (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j)) F := hFrac
  exact exists_ringEquiv_functionField_of_isFractionRing (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))
    (TwoChartIntegralModel.ιFin R F j) F

theorem finrank_eq_finrank_of_iotaFin_comp_eq
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hFrac : IsFractionRing ↥(TwoChartIntegralModel.chartAlgFin R F j) F)
    (hFrac' : IsFractionRing ↥(TwoChartIntegralModel.chartAlgFin R F' j') F')
    (φ : F →ₐ[R] F')
    (m : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) [IsFinite m]
    (hsurj : Function.Surjective m.base)
    (ιF : ↥(TwoChartIntegralModel.chartAlgFin R F j) →ₐ[R] ↥(TwoChartIntegralModel.chartAlgFin R F' j'))
    (hιF : ∀ x, (ιF x : F') = φ x)
    (hsq : Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ TwoChartIntegralModel.ιFin R F j = TwoChartIntegralModel.ιFin R F' j' ≫ m)
    (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) [Flat (m ∣_ V)] [LocallyOfFinitePresentation (m ∣_ V)]
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hy : y ∈ V) :
    m.finrank y = (letI := φ.toRingHom.toAlgebra; Module.finrank F F') := by
  haveI := AlgebraicCurve.TwoChartIntegralModel.isIntegral R F j
  haveI := AlgebraicCurve.TwoChartIntegralModel.isIntegral R F' j'
  obtain ⟨eF, heF⟩ := exists_ringEquiv_functionField_twoChartIntegralModel R F j hFrac
  obtain ⟨eF', heF'⟩ := exists_ringEquiv_functionField_twoChartIntegralModel R F' j' hFrac'
  let ψ : (AlgebraicCurve.TwoChartIntegralModel R F j).functionField →+* (AlgebraicCurve.TwoChartIntegralModel R F' j').functionField :=
    eF'.toRingHom.comp (φ.toRingHom.comp eF.symm.toRingHom)

  have hchart : (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F' j') F').comp ιF.toRingHom =
      φ.toRingHom.comp (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) F) := RingHom.ext fun x => hιF x

  have hψ : (AlgebraicCurve.TwoChartIntegralModel R F' j').fromSpecStalk (genericPoint _) ≫ m =
      Spec.map (CommRingCat.ofHom ψ) ≫ (AlgebraicCurve.TwoChartIntegralModel R F j).fromSpecStalk (genericPoint _) := by
    have hidF : eF.symm.toRingHom.comp eF.toRingHom = RingHom.id _ := by ext x; exact eF.symm_apply_apply x
    have hS : Spec.map (CommRingCat.ofHom eF.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom eF.toRingHom) = 𝟙 _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hidF, CommRingCat.ofHom_id, Spec.map_id]
    have hch : Spec.map (CommRingCat.ofHom (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F' j') F')) ≫
        Spec.map (CommRingCat.ofHom ιF.toRingHom) =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) F)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hchart]
    have hψS : Spec.map (CommRingCat.ofHom ψ) = Spec.map (CommRingCat.ofHom eF'.toRingHom) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom eF.symm.toRingHom) := by
      simp only [ψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    calc (AlgebraicCurve.TwoChartIntegralModel R F' j').fromSpecStalk (genericPoint _) ≫ m
        = Spec.map (CommRingCat.ofHom eF'.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F' j') F')) ≫
              Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ TwoChartIntegralModel.ιFin R F j := by
          rw [← heF', Category.assoc, Category.assoc, ← hsq]
      _ = Spec.map (CommRingCat.ofHom eF'.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) F)) ≫
              TwoChartIntegralModel.ιFin R F j := by
          rw [reassoc_of% hch]
      _ = Spec.map (CommRingCat.ofHom eF'.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
            (Spec.map (CommRingCat.ofHom eF.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom eF.toRingHom)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) F)) ≫
              TwoChartIntegralModel.ιFin R F j := by
          rw [hS, Category.id_comp]
      _ = Spec.map (CommRingCat.ofHom ψ) ≫ (AlgebraicCurve.TwoChartIntegralModel R F j).fromSpecStalk (genericPoint _) := by
          rw [hψS, Category.assoc, Category.assoc, Category.assoc, heF]
  rw [AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict m hsurj ψ hψ V y hy]
  letI := φ.toRingHom.toAlgebra
  letI := ψ.toAlgebra
  symm
  refine Algebra.finrank_eq_of_equiv_equiv eF eF' ?_
  ext x
  show ψ (eF x) = eF' (φ x)
  simp only [ψ, RingHom.comp_apply]
  rw [show eF.symm.toRingHom (eF x) = x from eF.symm_apply_apply x]
  rfl

end H5Aux

namespace H5Aux

theorem morphismRestrict_isoComp_iff {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {X' X Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e] (m : X ⟶ Y) (V : Y.Opens) :
    P ((e ≫ m) ∣_ V) ↔ P (m ∣_ V) := by
  rw [morphismRestrict_comp]
  have hiso : IsIso (e ∣_ m ⁻¹ᵁ V) := (isPullback_morphismRestrict e (m ⁻¹ᵁ V)).isIso_fst_of_isIso
  haveI := hiso
  exact MorphismProperty.cancel_left_of_respectsIso P (e ∣_ m ⁻¹ᵁ V) (m ∣_ V)

theorem flat_morphismRestrict_isoComp_iff {X' X Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e] (m : X ⟶ Y) (V : Y.Opens) :
    Flat ((e ≫ m) ∣_ V) ↔ Flat (m ∣_ V) :=
  morphismRestrict_isoComp_iff (P := @Flat) e m V

theorem locallyOfFinitePresentation_morphismRestrict_isoComp_iff {X' X Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e] (m : X ⟶ Y)
    (V : Y.Opens) :
    LocallyOfFinitePresentation ((e ≫ m) ∣_ V) ↔ LocallyOfFinitePresentation (m ∣_ V) :=
  morphismRestrict_isoComp_iff (P := @LocallyOfFinitePresentation) e m V

theorem finrank_isoComp_eq {X' X Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e] (m : X ⟶ Y) [IsFinite m] (V : Y.Opens)
    [Flat (m ∣_ V)] (y : Y) (hy : y ∈ V) :
    (e ≫ m).finrank y = m.finrank y := by
  haveI : Flat ((e ≫ m) ∣_ V) := (flat_morphismRestrict_isoComp_iff e m V).mpr inferInstance
  haveI : IsFinite (e ≫ m) := inferInstance
  rw [← AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank (e ≫ m) V y hy,
    ← AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank m V y hy]
  have h : (e ≫ m) ∣_ V = (e ∣_ m ⁻¹ᵁ V) ≫ m ∣_ V := morphismRestrict_comp e m V
  have hiso : IsIso (e ∣_ m ⁻¹ᵁ V) := (isPullback_morphismRestrict e (m ⁻¹ᵁ V)).isIso_fst_of_isIso
  rw [h]
  haveI := hiso
  exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso (e ∣_ m ⁻¹ᵁ V) (m ∣_ V)) ⟨y, hy⟩

end H5Aux

namespace H5Asm
open AlgebraicCurve.TwoChartIntegralModel

def restrictA (A : Type) {L : Type} [CommRing A] [Field L] [Algebra A L] {E E' : Type} [Field E] [Field E']
    [Algebra L E] [Algebra L E'] [Algebra A E] [Algebra A E'] [IsScalarTower A L E] [IsScalarTower A L E']
    (f : E →ₐ[L] E') : E →ₐ[A] E' :=
  { f.toRingHom with
    commutes' := fun a => by
      change f (algebraMap A E a) = algebraMap A E' a
      rw [IsScalarTower.algebraMap_eq A L E, IsScalarTower.algebraMap_eq A L E', RingHom.comp_apply, RingHom.comp_apply,
        AlgHom.commutes] }

theorem restrictA_apply {A L : Type} [CommRing A] [Field L] [Algebra A L] {E E' : Type} [Field E] [Field E']
    [Algebra L E] [Algebra L E'] [Algebra A E] [Algebra A E'] [IsScalarTower A L E] [IsScalarTower A L E']
    (f : E →ₐ[L] E') (x : E) : restrictA A f x = f x := rfl

end H5Asm

open H5Asm AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 6400000 in
theorem solution_ac
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (hβ : ModularCurve.HeckeBetaOneDefined (M * p) ℓ) :
    ∃ (πα πβ : SchemeHomOver (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j))
      (_ : IsFinite πα.1) (_ : IsFinite πβ.1) (_ : LocallyOfFinitePresentation πα.1) (_ : LocallyOfFinitePresentation πβ.1)
      (ια ιβ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
      (U : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).Opens),

      Function.Surjective πα.1.base ∧ Function.Surjective πβ.1.base ∧

      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (((ια b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L)) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (((ιβ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
        ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L)) ∧
      AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j ∧
      AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j ∧

      πα.1 ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).opensRange = (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange ∧
      πβ.1 ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).opensRange = (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange ∧

      (∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j), ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U) ∧
      Flat (πα.1 ∣_ U) ∧ Flat (πβ.1 ∣_ U) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j), y ∈ U → πα.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1)) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1)) := by
  subst hK

  let α : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) →ₐ[A] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) :=
    restrictA A (ModularCurve.heckeAlphaOneBar L (M * p) ℓ)
  let β : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) →ₐ[A] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) :=
    restrictA A (ModularCurve.heckeBetaOneBarOf L (M * p) ℓ hβ)
  have hαcoe : ∀ x, ((α x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = (x : LaurentSeries L) := fun x =>
    ModularCurve.coe_heckeAlphaOneBar (L := L) (M * p) ℓ x
  have hβcoe : ∀ x, ((β x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ModularCurve.qExpand L ℓ (x : LaurentSeries L) := fun x =>
    ModularCurve.coe_heckeBetaOneBarOf (L := L) (M * p) ℓ hβ x
  have hαj : α j = jℓ := Subtype.ext (by rw [hαcoe, hj, hjℓ])
  let j' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) := β j
  have hj'coe : ((j' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq) := by
    rw [hβcoe, hj]
  haveI : Fact (j' ≠ 0) := ⟨fun h => by
    have h1 : ((j' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = 0 := by rw [h]; rfl
    rw [hβcoe, map_eq_zero_iff _ (ModularCurve.qExpand_injective (R := L) ℓ)] at h1
    exact (Fact.out : j ≠ 0) (Subtype.ext h1)⟩

  have hαfin : α.toRingHom.Finite :=
    H5Aux.finite_of_coe_eq _ _ rfl (H5Aux.finite_toRingHom_heckeAlphaOneBar L (M * p) ℓ)
  have hβfin : β.toRingHom.Finite :=
    H5Aux.finite_of_coe_eq (ModularCurve.heckeBetaOneBar L (M * p) ℓ).toRingHom _
      (by funext x
          change ModularCurve.heckeBetaOneBar L (M * p) ℓ x = ModularCurve.heckeBetaOneBarOf L (M * p) ℓ hβ x
          rw [ModularCurve.heckeBetaOneBar_eq (L := L) (M * p) ℓ hβ])
      (H5Aux.finite_toRingHom_heckeBetaOneBar L (M * p) ℓ hβ)

  have hT1 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L _ A j hj
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p)) hT1 L
      _ rfl j hj
  haveI := hFD
  haveI : PerfectField ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))))) := PerfectField.ofCharZero
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨hFT0, hFT0'⟩ := finiteType_chartAlgFin_and_chartAlgInf A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j htj hFD hsep
  haveI := hFT0; haveI := hFT0'
  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) = IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self L j⁻¹)
      rwa [inv_inv] at h
  haveI hAlg' : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) := by
    rw [hadj]; exact hAlg
  have hFfin : IsNoetherianRing ↥(chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j) ∧ IsFractionRing ↥(chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    ⟨Algebra.FiniteType.isNoetherianRing A _, isFractionRing_chartAlg A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) {j}⟩
  have hFinf : IsNoetherianRing ↥(chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j) ∧ IsFractionRing ↥(chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    ⟨Algebra.FiniteType.isNoetherianRing A _, isFractionRing_chartAlg A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) {j⁻¹}⟩

  obtain ⟨mα, ιFα, ιIα, hιFα, -, hmαb, hsqFα, -, hpreFα, -, hfinα, hsurjα, hιFαfin, hιIαfin, -, -⟩ :=
    exists_hom_isFinite_surjective_chartMap_finite_of_algHom A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) α hαfin j jℓ hαj hFfin hFinf

  obtain ⟨mβ, ιFβ, ιIβ, hιFβ, -, hmβb, hsqFβ, -, hpreFβ, -, hfinβ, hsurjβ, hιFβfin, hιIβfin, -, -⟩ :=
    exists_hom_isFinite_surjective_chartMap_finite_of_algHom A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) β hβfin j j' rfl hFfin hFinf

  have ftrans : ∀ {B C : Type} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (f : B →ₐ[A] C),
      f.toRingHom.Finite → Algebra.FiniteType A B → Algebra.FiniteType A C := by
    intro B C _ _ _ _ f hf hB
    letI := f.toRingHom.toAlgebra
    haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
    haveI : Module.Finite B C := hf
    exact Algebra.FiniteType.trans hB inferInstance
  haveI : Algebra.FiniteType A ↥(chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ) := ftrans ιFα hιFαfin hFT0
  haveI : Algebra.FiniteType A ↥(chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ) := ftrans ιIα hιIαfin hFT0'
  haveI : Algebra.FiniteType A ↥(chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j') := ftrans ιFβ hιFβfin hFT0
  haveI : Algebra.FiniteType A ↥(chartAlgInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j') := ftrans ιIβ hιIβfin hFT0'
  haveI := isIntegral A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ
  haveI := isIntegral A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j'
  haveI : IsProper (toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ) := isProper_toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ
  haveI : IsProper (toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j') := isProper_toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) j'
  obtain ⟨hO1fin, hO1fin', hvis, hvis'⟩ := H5Aux.o1_changeOfGenerator_inputs p M L A ℓ jℓ hjℓ j' hj'coe
  obtain ⟨w, ιFw, -, -, hιFw, hbijw, -, -, hwb, hsqw, -⟩ :=
    exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ j' hO1fin hO1fin' hvis hvis'

  let πβ' : AlgebraicCurve.TwoChartIntegralModel A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ ⟶ AlgebraicCurve.TwoChartIntegralModel A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j :=
    w.hom ≫ mβ
  have hπβb : πβ' ≫ toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j = toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ := by
    simp only [πβ', Category.assoc, hmβb, hwb]

  haveI : IsFinite mα := hfinα
  haveI : Surjective mα := ⟨hsurjα⟩
  haveI : IsFinite mβ := hfinβ
  haveI : IsFinite πβ' := inferInstance
  have hwsurj : Function.Surjective w.hom.base := (Scheme.homeoOfIso w).surjective
  have hsurjβ' : Function.Surjective πβ'.base := by
    intro z
    obtain ⟨y, hy⟩ := hsurjβ z
    obtain ⟨x, hx⟩ := hwsurj y
    exact ⟨x, by rw [← hy, ← hx, Scheme.Hom.comp_apply]⟩
  haveI : Surjective πβ' := ⟨hsurjβ'⟩
  haveI := isIntegral A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j
  haveI : IsLocallyNoetherian (AlgebraicCurve.TwoChartIntegralModel A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j) := by
    have hN : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] {X : Scheme.{0}} (f : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion f],
        IsNoetherianRing Γ(X, f.opensRange) := by
      intro C _ _ X f _
      exact isNoetherianRing_of_ringEquiv C
        ((Scheme.ΓSpecIso (CommRingCat.of C)).symm ≪≫ IsOpenImmersion.ΓIsoTop f).commRingCatIsoToRingEquiv
    haveI := hFfin.1; haveI := hFinf.1
    refine AlgebraicGeometry.isLocallyNoetherian_of_affine_cover
      (S := fun b : Bool => cond b ⟨chartFinOpen A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j, isAffineOpen_chartFinOpen A _ j⟩
        ⟨chartInfOpen A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j, isAffineOpen_chartInfOpen A _ j⟩) ?_ ?_
    · rw [iSup_bool_eq]; exact twoChartCover A _ j
    · rintro (_ | _)
      · exact hN _ (ιInf A _ j)
      · exact hN _ (ιFin A _ j)
  have hY := isIntegrallyClosed_stalk A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j
  obtain ⟨Vα, dα, hflα, hlfpα, hrkα, hVα⟩ :=
    AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite mα hY
  obtain ⟨Vβ, dβ, hflβ, hlfpβ, hrkβ, hVβ⟩ :=
    AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite πβ' hY
  haveI := hflα; haveI := hflβ; haveI := hlfpα; haveI := hlfpβ
  haveI : Flat (mα ∣_ (Vα ⊓ Vβ)) := H5Aux.flat_morphismRestrict_of_le mα inf_le_left
  haveI : Flat (πβ' ∣_ (Vα ⊓ Vβ)) := H5Aux.flat_morphismRestrict_of_le πβ' inf_le_right

  have hT2 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ) := by
    simp [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, ModularGroup.T]
  have hFDℓ := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ)) hT2 L
    (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) rfl jℓ hjℓ
  haveI := hFDℓ
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({jℓ} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hfrℓ : IsFractionRing ↥(chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) :=
    isFractionRing_chartAlg A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) {jℓ}
  have hdα : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j), y ∈ Vα → mα.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1) := by
    intro y hy
    rw [H5Aux.finrank_eq_finrank_of_iotaFin_comp_eq A _ _ j jℓ hFfin.2 hfrℓ α mα hsurjα ιFα hιFα hsqFα Vα y hy]
    exact ModularCurve.finrankAlong_heckeAlphaOneBar L (M * p) ℓ

  have hιβ : ∀ x, (((ιFw.comp ιFβ) x : ↥(chartAlgFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) = β x := fun x => by
    rw [AlgHom.comp_apply, hιFw, hιFβ]
  have hsqβ : Spec.map (CommRingCat.ofHom (ιFw.comp ιFβ).toRingHom) ≫ ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j = ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ ≫ πβ' := by
    show _ = ιFin A _ jℓ ≫ (w.hom ≫ mβ)
    rw [← Category.assoc, hsqw, Category.assoc, ← hsqFβ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hdβ : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j), y ∈ Vβ → πβ'.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1) := by
    intro y hy
    rw [H5Aux.finrank_eq_finrank_of_iotaFin_comp_eq A _ _ j jℓ hFfin.2 hfrℓ β πβ' hsurjβ' (ιFw.comp ιFβ) hιβ hsqβ Vβ y hy,
      ← ModularCurve.finrankAlong_heckeBetaOneBar L (M * p) ℓ hβ, ModularCurve.heckeBetaOneBar_eq (L := L) (M * p) ℓ hβ]
    rfl

  have hlfpA : LocallyOfFinitePresentation mα := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hlfpB : LocallyOfFinitePresentation πβ' := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

  have hιFwsurj : Function.Surjective (Spec.map (CommRingCat.ofHom ιFw.toRingHom)).base := by
    have hmap : Spec.map (CommRingCat.ofHom ιFw.toRingHom) = Spec.map ((RingEquiv.ofBijective ιFw hbijw).toCommRingCatIso.hom) := rfl
    haveI : IsIso (Spec.map (CommRingCat.ofHom ιFw.toRingHom)) := by rw [hmap]; infer_instance
    exact (Scheme.homeoOfIso (asIso (Spec.map (CommRingCat.ofHom ιFw.toRingHom)))).surjective
  have hpreβ : πβ' ⁻¹ᵁ (ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j).opensRange = (ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ).opensRange := by
    rw [Scheme.Hom.comp_preimage, hpreFβ]
    ext x
    constructor
    · rintro ⟨z', hz'⟩
      obtain ⟨z, rfl⟩ := hιFwsurj z'
      refine ⟨z, (Scheme.homeoOfIso w).injective ?_⟩
      have h1 := congrArg (fun φ => φ.base z) hsqw
      exact h1.trans hz'
    · rintro ⟨z, rfl⟩
      exact ⟨(Spec.map (CommRingCat.ofHom ιFw.toRingHom)).base z, (congrArg (fun φ => φ.base z) hsqw).symm⟩
  refine ⟨⟨mα, hmαb⟩, ⟨πβ', hπβb⟩, hfinα, inferInstance, hlfpA, hlfpB, ιFα, ιFw.comp ιFβ, Vα ⊓ Vβ,
    hsurjα, hsurjβ', ?_, ?_, hsqFα.symm, hsqβ.symm, hpreFα, hpreβ, ?_, inferInstance, inferInstance, ?_, ?_⟩
  ·
    intro b
    rw [hιFα, hαcoe]
  ·
    intro b
    rw [hιβ, hβcoe]
  ·
    intro x hx
    exact ⟨hVα x hx, hVβ x hx⟩
  · intro y hy
    exact hdα y hy.1
  · intro y hy
    exact hdβ y hy.2

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (hβ : ModularCurve.HeckeBetaOneDefined (M * p) ℓ) :
    ∃ (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (_ : IsFinite πα.1) (_ : IsFinite πβ.1) (_ : LocallyOfFinitePresentation πα.1) (_ : LocallyOfFinitePresentation πβ.1)
      (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
      (U : (ModularCurve.TwoChartModel A (↥K) j).Opens),

      Function.Surjective πα.1.base ∧ Function.Surjective πβ.1.base ∧

      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L)) ∧
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
        ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L)) ∧
      ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j ∧
      ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j ∧

      πα.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange ∧
      πβ.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange ∧

      (∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j), ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U) ∧
      Flat (πα.1 ∣_ U) ∧ Flat (πβ.1 ∣_ U) ∧
      (∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πα.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1)) ∧
      (∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1)) :=
  solution_ac p M hM hpM L ζ hζ K hK A hAp hζA j hj ℓ jℓ hjℓ hβ

end S_ModularCurve_XOneP_exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul (solution)
