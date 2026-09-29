-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bc915f06-1269-5a41-b1fa-2c0192d17aa4

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_XHHeckeOperator
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
import Theorems.Thm_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
import Theorems.Thm_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard

open scoped MatrixGroups

namespace GenFibL3
open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem gamma0_le_gamma0_of_dvd {M N : ℕ} (h : N ∣ M) : Gamma0 M ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have : ((A 1 0 : ℤ) : ZMod N) = ZMod.castHom h (ZMod N) ((A 1 0 : ℤ) : ZMod M) := by simp
  rw [this, hA, map_zero]

theorem unitsMap_gamma0Units {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) (A : SL(2, ℤ)) (hA : A ∈ Gamma0 M) :
    ZMod.unitsMap h (gamma0Units M ⟨A, hA⟩) = gamma0Units N ⟨A, gamma0_le_gamma0_of_dvd h hA⟩ := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map, val_gamma0Units, val_gamma0Units]
  show ZMod.castHom h (ZMod N) (Gamma0Map M ⟨A, hA⟩) = Gamma0Map N ⟨A, _⟩
  simp [Gamma0Map]

theorem gammaH_infSubgroup_inf_gamma0_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 M = GammaH M H := by
  ext A
  rw [Subgroup.mem_inf, mem_GammaH_iff, mem_GammaH_iff]
  constructor
  · rintro ⟨⟨hA', hu'⟩, hA⟩
    refine ⟨hA, ?_⟩
    rw [infSubgroup, Subgroup.mem_map] at hu'
    obtain ⟨h, hh, hhu⟩ := hu'
    have key : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (gamma0Units M ⟨A, hA⟩ * h⁻¹) = 1 := by
      rw [map_mul, map_inv, unitsMap_gamma0Units (Nat.div_dvd_of_dvd hpM) A hA, ← hhu, mul_inv_cancel]
    have hmem := hHp _ key
    have : gamma0Units M ⟨A, hA⟩ = gamma0Units M ⟨A, hA⟩ * h⁻¹ * h := by rw [inv_mul_cancel_right]
    rw [this]
    exact H.mul_mem hmem hh
  · rintro ⟨hA, hu⟩
    refine ⟨⟨gamma0_le_gamma0_of_dvd (Nat.div_dvd_of_dvd hpM) hA, ?_⟩, hA⟩
    rw [infSubgroup, Subgroup.mem_map]
    exact ⟨_, hu, unitsMap_gamma0Units (Nat.div_dvd_of_dvd hpM) A hA⟩

theorem exists_algHom_laurentBaseChange_coe_eq_of_eq (T T' : IntermediateField ℚ (LaurentSeries ℚ)) (h : T = T') :
    ∃ ι : ↥(laurentBaseChange (AlgebraicClosure ℚ) T) →ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) T'),
      (∀ u : ↥(laurentBaseChange (AlgebraicClosure ℚ) T),
        ((ι u : ↥(laurentBaseChange (AlgebraicClosure ℚ) T')) : LaurentSeries (AlgebraicClosure ℚ)) =
          (u : LaurentSeries (AlgebraicClosure ℚ))) ∧ Function.Surjective ι := by
  subst h
  exact ⟨AlgHom.id (AlgebraicClosure ℚ) _, fun _ => rfl, Function.surjective_id⟩

theorem ofPoint_I_congr {𝒞 S T : Scheme.{0}} (f : 𝒞 ⟶ S) [IsSeparated f] {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (h : a = a') (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I = (RelEffCartierDiv.ofPoint f a' (h ▸ ha)).I := by
  subst h; rfl

theorem finrankAlong_eq_one_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : finrankAlong K φ = 1 := by
  letI := algebraAlong φ
  have hb : Function.Bijective (Algebra.linearMap F F') := ⟨φ.toRingHom.injective, hφ⟩
  have e : F ≃ₗ[F] F' := LinearEquiv.ofBijective (Algebra.linearMap F F') hb
  show Module.finrank F F' = 1
  rw [← e.finrank_eq, Module.finrank_self]

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply Gamma1_le_GammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

theorem restrictAlong_comp {K F₁ F₂ F₃ : Type*} [Field K] [Field F₁] [Field F₂] [Field F₃]
    [Algebra K F₁] [Algebra K F₂] [Algebra K F₃]
    (φ : F₁ →ₐ[K] F₂) (ψ : F₂ →ₐ[K] F₃) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψφ : (ψ.comp φ).toRingHom.IsIntegral) (v : Place K F₃) :
    v.restrictAlong (ψ.comp φ) hψφ = (v.restrictAlong ψ hψ).restrictAlong φ hφ :=
  Place.ext rfl

theorem finiteDimensional_adjoin_congr_inst {F : Type*} [Field F] {i₁ i₂ : Algebra ℚ F} (j : F)
    (h : letI := i₁; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F) :
    letI := i₂; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F := by
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this
  exact h

theorem transcendental_of_ringHom {A B : Type*} [Field A] [Field B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →+* B) {a : A} (h : Transcendental ℚ (f a)) : Transcendental ℚ a := by
  intro halg
  apply h
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  have := Polynomial.aeval_algHom_apply f.toRatAlgHom a P
  rw [hP, map_zero] at this
  exact this

theorem isIntegral_of_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) :
    σ.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ σ.surjective

theorem mapOnProdOver_comp_curveChange {R : Type} [CommRing R] {C C' : Scheme.{0}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} (π : C' ⟶ C) (hπ : π ≫ c = c')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (φ : T ⟶ T') (hφ : φ ≫ t' = t) :
    mapOnProdOver c' φ hφ ≫ curveChange π hπ t' = curveChange π hπ t ≫ mapOnProdOver c φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, curveChange, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
      mapOnProdOver_fst, mapOnProdOver_fst_assoc]
  · simp only [Category.assoc, curveChange, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      mapOnProdOver_snd, mapOnProdOver_snd_assoc]

theorem comap_comap_eq_comap_of_ideal_identity {R : Type} [CommRing R] {C C' : Scheme.{0}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} [IsSeparated c] [IsSeparated c']
    (π : C' ⟶ C) (hπ : π ≫ c = c')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (φ : T ⟶ T') (hφ : φ ≫ t' = t) [IsAffineHom φ]
    (u : T' ⟶ C') (hu : u ≫ c' = t') {k : ℕ} (u' : Fin k → (T' ⟶ C')) (hu' : ∀ j, u' j ≫ c' = t') (e : Fin k → ℕ)
    (y : T ⟶ C') (hy : φ ≫ u = y) (y' : Fin k → (T ⟶ C')) (hy' : ∀ j, φ ≫ u' j = y' j)
    (hyc : y ≫ c' = t) (hy'c : ∀ j, y' j ≫ c' = t) (hyπ : (y ≫ π) ≫ c = t)
    (hideal : (RelEffCartierDiv.ofPoint c (y ≫ π) hyπ).I.comap (curveChange π hπ t) =
      (RelEffCartierDiv.ofPoint c' y hyc).I * ∏ j, (RelEffCartierDiv.ofPoint c' (y' j) (hy'c j)).I ^ (e j))
    (huπ : (u ≫ π) ≫ c = t') :
    ((RelEffCartierDiv.ofPoint c (u ≫ π) huπ).I.comap (curveChange π hπ t')).comap (mapOnProdOver c' φ hφ) =
      ((RelEffCartierDiv.ofPoint c' u hu).I * ∏ j, (RelEffCartierDiv.ofPoint c' (u' j) (hu' j)).I ^ (e j)).comap
        (mapOnProdOver c' φ hφ) := by
  subst hy
  obtain rfl : y' = fun j => φ ≫ u' j := funext fun j => (hy' j).symm
  have hS1 := (AlgebraicGeometry.RelEffCartierDiv.comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow c φ hφ (u ≫ π) huπ
    (ι := Fin 0) Fin.elim0 (fun i => i.elim0) Fin.elim0).1
  have hS2 := (AlgebraicGeometry.RelEffCartierDiv.comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow c' φ hφ u hu u' hu' e).2
  rw [hS2, ← Scheme.IdealSheafData.comap_comp, mapOnProdOver_comp_curveChange π hπ φ hφ, Scheme.IdealSheafData.comap_comp, hS1,
    ofPoint_I_congr c (Category.assoc φ u π).symm]
  exact hideal

end GenFibL3

open GenFibL3 in
set_option maxHeartbeats 12800000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n) :
    ∃ (k : ℕ) (u' : Fin k → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)) (e : Fin k → ℕ),
      (∀ j, 0 < e j) ∧ ∑ j, e j = p ∧
      (∀ j, ∃ y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
        Spec.map (CommRingCat.ofHom A.subtype) ≫ (u' j).1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧ y' ≠ y) ∧
      (∀ j, (u' j).1 ≫ 𝔛.π.1 = u.1 ≫ 𝔛.π.1) ∧
      (∀ j, Set.range (u' j).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
      (∀ j, ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (u' j).1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
            (𝔛.Mfib A hA ρ hρ).placeOfPoint P) ∧

      𝔛.π.1.finrank ((Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 ≫ 𝔛.π.1).base
        (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) = p + 1 ∧

      ((RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (u.1 ≫ 𝔛.π.1)
          ((Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2))).I.comap
          (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ)))).comap
          (mapOnProdOver (toBase p (ΓM M H) hj)
            (g' := Spec.map (CommRingCat.ofHom ρ)) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (Spec.map (CommRingCat.ofHom A.subtype)) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) =
        ((RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I *
          ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u' j).1 (u' j).2).I ^ (e j)).comap
          (mapOnProdOver (toBase p (ΓM M H) hj)
            (g' := Spec.map (CommRingCat.ofHom ρ)) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (Spec.map (CommRingCat.ofHom A.subtype)) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (ΓM M H).FiniteIndex := finiteIndex_GammaH M H
  haveI : (ΓN p M H hpM).FiniteIndex := finiteIndex_GammaH (M / p) (infSubgroup p M H hpM)
  have hTM : ModularGroup.T ∈ ΓM M H := T_mem_GammaH M H
  have hTN : ModularGroup.T ∈ ΓN p M H hpM := T_mem_GammaH (M / p) (infSubgroup p M H hpM)

  have hle : ΓM M H ≤ ΓN p M H hpM := ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  have hFle : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H :=
    IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hle))
  let αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H) :=
    IntermediateField.inclusion hFle
  have hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun u => IntermediateField.coe_inclusion hFle u
  have hfinα : FiniteAlong (AlgebraicClosure ℚ) αH :=
    ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) hTN hTM αH
  have hαint : αH.toRingHom.IsIntegral := by
    letI := algebraAlong αH
    haveI : Module.Finite ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := hfinα
    intro x
    exact Algebra.IsIntegral.isIntegral (R := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) x

  have htj : Transcendental ℚ (jAt (ΓN p M H hpM) hj) :=
    transcendental_of_ringHom (SubringClass.subtype (qExpFunctionFieldC ℚ (ΓN p M H hpM)))
      (ModularCurve.transcendental_jqModC ℚ :
        Transcendental ℚ (SubringClass.subtype (qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)))
  have hfd0 := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (ΓN p M H hpM) hTN
    (ΓN p M H hpM) le_rfl (fun γ h => Or.inl h) (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)).1
  have hfd : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (ΓN p M H hpM) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))))
      ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) :=
    finiteDimensional_adjoin_congr_inst _ hfd0
  have hreg := ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC (ΓN p M H hpM)
  obtain ⟨Meta₀, eeta₀, hiso₀, heeta₀, -, hne₀, pin₀⟩ :=
    ModularCurve.exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
      (qExpFunctionFieldC ℚ (ΓN p M H hpM)) p (jAt (ΓN p M H hpM) hj) htj hfd hreg
  haveI := hiso₀
  haveI := hne₀

  obtain ⟨hcoM, heftM⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  obtain ⟨hcoN, heftN⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM)
  haveI := hcoM; haveI := heftM; haveI := hcoN; haveI := heftN

  obtain ⟨hπfin, hπlfp, hπflat, hπrk⟩ := ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi p M H hpM hpM2 hHp hj 𝔛
  haveI := hπfin; haveI := hπlfp; haveI := hπflat
  haveI : IsFinite (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) :=
    MorphismProperty.pullback_map (P := @IsFinite) (f := toBase p (ΓM M H) hj) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      (f' := toBase p (ΓN p M H hpM) hj) (g' := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (i₁ := 𝔛.π.1) (i₂ := 𝟙 _)
      hπfin inferInstance 𝔛.π.2.symm (Category.id_comp _).symm
  haveI : Flat (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) :=
    MorphismProperty.pullback_map (P := @Flat) (f := toBase p (ΓM M H) hj) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      (f' := toBase p (ΓN p M H hpM) hj) (g' := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (i₁ := 𝔛.π.1) (i₂ := 𝟙 _)
      hπflat inferInstance 𝔛.π.2.symm (Category.id_comp _).symm
  haveI : LocallyOfFinitePresentation (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) :=
    MorphismProperty.pullback_map (P := @LocallyOfFinitePresentation) (f := toBase p (ΓM M H) hj) (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      (f' := toBase p (ΓN p M H hpM) hj) (g' := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) (i₁ := 𝔛.π.1) (i₂ := 𝟙 _)
      hπlfp inferInstance 𝔛.π.2.symm (Category.id_comp _).symm

  obtain ⟨V, huV, hV⟩ := ModularCurve.XHDRModelAtP.exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
    p M H hpM hj 𝔛 A hA ρ hρ y u hu uκ huκ₁ huκ₂ P hP hP₀
  have hyV : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ V := by
    rw [← hu]
    exact huV ⟨_, rfl⟩
  have hw₀ : Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace y) = 1 :=
    ModularCurve.XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
      p M H hpM hj 𝔛 αH hαq hαint Meta₀ eeta₀ heeta₀ hne₀ pin₀ y V hyV hV

  have hinert : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.inertiaDegAlong αH hαint = 1 := fun W =>
    ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (ΓM M H) hTM (xHFunctionField M H) rfl αH hαint W
  have hsep : SeparableAlong (AlgebraicClosure ℚ) αH := AlgebraicCurve.separableAlong_of_charZero αH hαint
  have hn : finrankAlong (AlgebraicClosure ℚ) αH = p + 1 := by

    have hpN : ¬ p ∣ M / p := by
      intro h
      apply hpM2
      obtain ⟨c, hc⟩ := h
      refine ⟨c, ?_⟩
      have := Nat.div_mul_cancel hpM
      rw [← this, hc]; ring
    have hΓ : CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * p) = CohCarrier.GammaH M H := by
      rw [Nat.div_mul_cancel hpM]; exact gammaH_infSubgroup_inf_gamma0_eq p M H hpM hHp
    have hT : xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) = xHFunctionField M H := by
      show qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * p)) =
        qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)
      rw [hΓ]
    obtain ⟨κ, hκcoe, hκs⟩ := exists_algHom_laurentBaseChange_coe_eq_of_eq _ _ hT
    have hcomp : κ.comp (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p) = αH := by
      apply AlgHom.ext
      intro v
      apply Subtype.ext
      rw [hαq, AlgHom.comp_apply, hκcoe, ModularCurve.coe_heckeAlphaHBar]
    rw [← hcomp, AlgebraicCurve.finrankAlong_comp, ModularCurve.finrankAlong_heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) hpN,
      finrankAlong_eq_one_of_surjective κ hκs, mul_one]
  obtain ⟨k, W, e, hepos, hesum, hWinj, hWne, hWfib, hWall, heW, -⟩ :=
    AlgebraicCurve.Divisor.exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
      αH hαint hfinα hsep p hn hinert (𝔛.Meta.pointEquivPlace y) hw₀
  let pl := 𝔛.Meta.pointEquivPlace
  let y' : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} := fun j => pl.symm (W j)
  have hply' : ∀ j, pl (y' j) = W j := fun j => pl.apply_symm_apply (W j)
  have hinj : Function.Injective y' := fun a b h => hWinj (by rw [← hply' a, ← hply' b]; exact congrArg pl h)
  have hne : ∀ j, y' j ≠ y := fun j h => hWne j (by rw [← hply' j, h])
  have hfib : ∀ j, (pl (y' j)).restrictAlong αH hαint = (pl y).restrictAlong αH hαint := fun j => by rw [hply']; exact hWfib j
  have hall : ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      w.restrictAlong αH hαint = (pl y).restrictAlong αH hαint → w ≠ pl y → ∃ j, w = pl (y' j) := fun w hw hwne => by
    obtain ⟨j, hj'⟩ := (hWall w hw).resolve_left hwne
    exact ⟨j, by rw [hply']; exact hj'⟩
  have he : ∀ j, e j = Place.ramificationIndexAlong αH (pl (y' j)) := fun j => by rw [hply']; exact (heW j).symm

  obtain ⟨hover, hideal⟩ :=
    ModularCurve.XHDRModelAtP.comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
      p M H hpM hj 𝔛 αH hαq hαint Meta₀ eeta₀ heeta₀ hne₀ pin₀ y hw₀ k y' e hinj hne hfib hall he

  have h94 := fun j => (ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
    p M H hpM hj 𝔛 A hA ρ hρ y u hu uκ huκ₁ huκ₂ P hP hP₀ (y' j) (hover j) (hne j)).2
  choose u' hu' hπ' husm' huκ' using h94
  refine ⟨k, u', e, hepos, hesum, fun j => ⟨y' j, hu' j, hne j⟩, hπ', husm', fun j => ?_, ?_, ?_⟩
  · obtain ⟨uκ', h1, h2, -, P', hP', hfr⟩ := huκ' j
    exact ⟨uκ', h1, h2, P', hP', hfr⟩
  ·
    exact hπrk _
  ·
    exact comap_comap_eq_comap_of_ideal_identity 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom A.subtype))
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) u.1 u.2 (fun j => (u' j).1) (fun j => (u' j).2) e
      (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) hu (fun j => (y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) hu' _ _ _ hideal _

end S_ModularCurve_XHDRModelAtP_exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow (solution)
