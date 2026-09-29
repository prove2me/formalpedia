-- Prove2me | solution 1 for ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0225dfcc-c8aa-5096-bbed-8390d4f1259a

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace

import Theorems.Thm_AlgebraicGeometry_exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one
import Theorems.Thm_ModularCurve_exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_KaehlerDifferential_exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq
import Theorems.Thm_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExpBar
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul_map_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_AlgebraicGeometry_exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
import Theorems.Thm_ModularCurve_exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve P2MW.S_ModularCurve_exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero.ModularCurve AlgebraicCurve IsLocalRing CuspForm"

universe u

namespace PowerSeries p2m_export "PowerSeries" "coeff_mk mk coeff_zero_X_mul map_comp coeff_coe coeff_map isUnit_iff_constantCoeff ext coeff_succ_mul_X map C coeff_succ_X_mul coeff X map_injective eq_mul_inv_iff_mul_eq toSubring algebraMap_eq" end PowerSeries
p2m_open_scoped "PowerSeries" in
theorem PowerSeries.map_map' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (Q : PowerSeries R) : (Q.map f).map g = Q.map (g.comp f) := by
  rw [PowerSeries.map_comp]; rfl

namespace ModularCurve p2m_export "ModularCurve" "qEuler diffQExp_smul_D diffQExpBar arithmeticGalois modularFunctionFieldBar modularFunctionFieldFull coeffEmb IsPlaceReductionModL coeffMap_ofPowerSeries modularFunctionFieldFullC baseChangeEquiv baseChangeEquiv_one_tmul cuspInftyFull exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.qEuler_ofPowerSeries {K : Type*} [CommRing K] (v : PowerSeries K) :
    ModularCurve.qEuler K (HahnSeries.ofPowerSeries ℤ K v) =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => (n : K) * PowerSeries.coeff n v) := by
  ext n
  change ((n : K) * (HahnSeries.ofPowerSeries ℤ K v).coeff n) = _
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [mul_zero]
  · rw [PowerSeries.coeff_mk]
    congr 1
    have : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg (not_lt.mp h)
    rw [← Int.cast_natCast (R := K), this]

set_option maxHeartbeats 6400000 in

theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))
        (ω : ↥((𝒱.kaehlerSections c).H0)) (P : PowerSeries ↥(GaloisRep.ratLocalizedAt p))
    (hP : diffQExpBar N (res ω) =
      HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ)
        ((((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • P).map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) :
    ∃ ω' : ↥((𝒱.kaehlerSections c).H0), ω = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • ω' := by

  haveI hloc : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing (Fact.out : p.Prime)

  set s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) := IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt p) with hsdef
  have hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal ↥(GaloisRep.ratLocalizedAt p))

  have hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s := by
    haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

    set η₀ : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) :=
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).base (IsLocalRing.closedPoint ℚ) with hη₀
    have hP : (e₀ ≫ pullback.fst c _).base x₀.1 = εinf.1.base η₀ := by
      rw [← hyx₀]
      have h1 : (e₀ ≫ pullback.fst c _).base ((y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ)) =
          ((y ≫ inv e₀) ≫ e₀ ≫ pullback.fst c _).base (IsLocalRing.closedPoint ℚ) := by
        simp only [Scheme.Hom.comp_base, TopCat.comp_app]
      rw [h1]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [hyε]
      simp only [Scheme.Hom.comp_base, TopCat.comp_app]
      rfl
    have hgen : η₀ ⤳ s := by
      refine (PrimeSpectrum.le_iff_specializes η₀ s).mp ?_
      show η₀.asIdeal ≤ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p)
      exact IsLocalRing.le_maximalIdeal η₀.2.ne_top
    rw [hP]
    exact hgen.map εinf.1.continuous

  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) := ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp
      (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).toAlgebra

  obtain ⟨π, t, u, hπker, hπt, hcot, hu, hu0, hu1⟩ := ModularCurve.exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec
  obtain ⟨-, -, -, -, -, hfin⟩ :=
    AlgebraicGeometry.exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one
      c εinf.1 εinf.2 s hs
  haveI := hfin
  have hπι : ∀ r : ↥(GaloisRep.ratLocalizedAt p), π.toRingHom ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))) = r := fun r => π.commutes r

  obtain ⟨ω_s, Exp, hExpR, hExpRoute, hresω⟩ :=
    ModularCurve.exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero
      N p hpN ι₀ c 𝒱 M₀ e₀ he₀ hgen0 ι hιdef hιR res hres εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec ω
  have key : ∀ ω_x : Ω[X.presheaf.stalk (εinf.1.base s)⁄↥(GaloisRep.ratLocalizedAt p)],
      KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR ω_x = res ω →
      ∃ η : Ω[X.presheaf.stalk (εinf.1.base s)⁄↥(GaloisRep.ratLocalizedAt p)], ω_x = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • η := by
    intro ω_x hΦ
    obtain ⟨g, hg⟩ := KaehlerDifferential.exists_eq_smul_D_of_retraction_of_ker_le_span_sup_sq π t hπt hcot ω_x

    obtain ⟨G, hG⟩ :=
      ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
        N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec g

    have hE1 : diffQExpBar N (res ω) =
        ((Exp g : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) *
          qEuler (AlgebraicClosure ℚ) ((Exp t : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← hΦ, hg, KaehlerDifferential.mapOfRingHom_smul_D]
      exact ModularCurve.diffQExp_smul_D (modularFunctionFieldBar N) (Exp g) (Exp t)

    have hcoeffEmb : ∀ v : PowerSeries ↥(GaloisRep.ratLocalizedAt p),
        coeffEmb (AlgebraicClosure ℚ) (HahnSeries.ofPowerSeries ℤ ℚ (v.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) =
          HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (v.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
      intro v
      rw [coeffEmb, ModularCurve.coeffMap_ofPowerSeries, PowerSeries.map_map', ← IsScalarTower.algebraMap_eq]
    have hExpg : ((Exp g : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (G.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
      rw [hExpRoute, ← hcoeffEmb, ← hG]; rfl
    have hExpt : ((Exp t : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (u.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
      rw [hExpRoute, ← hcoeffEmb, ← hu]; rfl

    set W : PowerSeries ↥(GaloisRep.ratLocalizedAt p) := PowerSeries.mk fun n => (n : ↥(GaloisRep.ratLocalizedAt p)) * PowerSeries.coeff n u with hW
    have hWmap : HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (W.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) =
        qEuler (AlgebraicClosure ℚ) (HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ)
          (u.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) := by
      rw [ModularCurve.qEuler_ofPowerSeries]
      congr 1
      ext n
      simp [hW, PowerSeries.coeff_mk, PowerSeries.coeff_map]
    have hGW : G * W = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • P := by
      haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
      have hinjR : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
        rw [IsScalarTower.algebraMap_eq ↥(GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
        exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ)
      apply PowerSeries.map_injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) hinjR
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := AlgebraicClosure ℚ)
      rw [map_mul, map_mul, hWmap, ← hExpg, ← hExpt, ← hE1, hP]

    obtain ⟨G', hG'⟩ : ∃ G' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), G = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • G' := by
      set W₁ : PowerSeries ↥(GaloisRep.ratLocalizedAt p) := PowerSeries.mk fun n => ((n + 1 : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * PowerSeries.coeff (n + 1) u with hW₁
      have hWX : W = PowerSeries.X * W₁ := by
        ext n
        rcases n with _ | n
        · simp [hW, hW₁, PowerSeries.coeff_zero_X_mul]
        · rw [PowerSeries.coeff_succ_X_mul]; simp [hW, hW₁]
      have hW₁u : IsUnit W₁ := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simpa [hW₁] using hu1
      obtain ⟨V, hV⟩ := hW₁u
      have hGX : G * PowerSeries.X = (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • P) * ((V⁻¹ : (PowerSeries ↥(GaloisRep.ratLocalizedAt p))ˣ) : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) := by
        rw [Units.eq_mul_inv_iff_mul_eq, mul_assoc, hV, ← hWX, hGW]
      refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (P * ((V⁻¹ : (PowerSeries ↥(GaloisRep.ratLocalizedAt p))ˣ) : PowerSeries ↥(GaloisRep.ratLocalizedAt p))), ?_⟩
      ext n
      have h := congrArg (PowerSeries.coeff (n + 1)) hGX
      rw [PowerSeries.coeff_succ_mul_X, smul_mul_assoc, map_smul] at h
      rw [h, map_smul, PowerSeries.coeff_mk]

    have hP2b : ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
            ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom g))) :
            ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
          HahnSeries.ofPowerSeries ℤ ℚ (((((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) • G').map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
      rw [hG, hG']
    obtain ⟨g', hg'⟩ :=
      ModularCurve.exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero
        N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec π.toRingHom hπι hπker t hπt hcot u hu hu0 hu1 g G' hP2b

    refine ⟨g' • KaehlerDifferential.D ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) t, ?_⟩
    rw [hg, hg', mul_smul]
    exact (algebraMap_smul (X.presheaf.stalk (εinf.1.base s)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (g' • KaehlerDifferential.D ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) t)).symm

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  obtain ⟨hfl0, hfl1, hfl01⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_kaehlerDifferential_cover_of_smooth 𝒱 c
  haveI := hfl0; haveI := hfl1; haveI := hfl01
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  set qκ : ↥(GaloisRep.ratLocalizedAt p) →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp (ρ A hA) with hqκ
  have hmaxR : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p (Fact.out)
  have hker : RingHom.ker qκ = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by
    apply le_antisymm
    · rw [← hmaxR]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top qκ)
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hqκ, RingHom.comp_apply, map_natCast,
        IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
      first | exact hA | simpa [ValuationSubring.LiesOverPrime] using hA
  have hmax : (Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} : Ideal ↥(GaloisRep.ratLocalizedAt p)).IsMaximal := by
    rw [← hmaxR]; exact IsLocalRing.maximalIdeal.isMaximal ↥(GaloisRep.ratLocalizedAt p)
  haveI hes' := hes_iso A hA
  haveI hint : IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom qκ))) :=
    IsIntegral.of_isIso (es A hA)
  have hx : εinf.1.base s ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom qκ))).base := by

    have hsq : (Spec.map (CommRingCat.ofHom qκ) ≫ εinf.1) ≫ c =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom qκ) := by
      rw [Category.assoc, εinf.2, Category.id_comp, Category.comp_id]
    refine ⟨(Limits.pullback.lift (Spec.map (CommRingCat.ofHom qκ) ≫ εinf.1) (𝟙 _) hsq).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)), ?_⟩
    have h1 : (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom qκ))).base
        ((Limits.pullback.lift (Spec.map (CommRingCat.ofHom qκ) ≫ εinf.1) (𝟙 _) hsq).base
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A))) =
        (Limits.pullback.lift (Spec.map (CommRingCat.ofHom qκ) ≫ εinf.1) (𝟙 _) hsq ≫
          Limits.pullback.fst c (Spec.map (CommRingCat.ofHom qκ))).base
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) := by
      simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [h1, Limits.pullback.lift_fst]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    congr 1

    apply PrimeSpectrum.ext
    show Ideal.comap qκ (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)).asIdeal = s.asIdeal
    rw [show (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)).asIdeal = ⊥ from
      IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker, ← hmaxR]
    rfl
  have hc0 : ∀ h0 : εinf.1.base s ∈ 𝒱.U0, ((X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom :
        (𝒱.cover c).A0 →+* X.presheaf.stalk (εinf.1.base s)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp (c.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) := by
    intro h0
    refine RingHom.ext fun r => ?_
    show (X.presheaf.germ 𝒱.U0 _ h0).hom ((c.appLE ⊤ 𝒱.U0 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) =
      (X.presheaf.germ ⊤ _ trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, ← CommRingCat.comp_apply (X.presheaf.map _),
      TopCat.Presheaf.germ_res]
    rfl
  have hc1 : ∀ h1 : εinf.1.base s ∈ 𝒱.U1, ((X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom :
        (𝒱.cover c).A1 →+* X.presheaf.stalk (εinf.1.base s)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A1) =
      ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp (c.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) := by
    intro h1
    refine RingHom.ext fun r => ?_
    show (X.presheaf.germ 𝒱.U1 _ h1).hom ((c.appLE ⊤ 𝒱.U1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) =
      (X.presheaf.germ ⊤ _ trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, ← CommRingCat.comp_apply (X.presheaf.map _),
      TopCat.Presheaf.germ_res]
    rfl

  have hβ0 : ∀ h0 : εinf.1.base s ∈ 𝒱.U0,
      Exp.comp ((X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom : (𝒱.cover c).A0 →+* X.presheaf.stalk (εinf.1.base s)) = ι := by
    intro h0
    refine RingHom.ext fun a => ?_
    apply Subtype.val_injective
    change ((Exp ((X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom a) : ↥(modularFunctionFieldBar N)) :
        LaurentSeries (AlgebraicClosure ℚ)) = ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ))
    rw [hExpRoute, hιdef]
    congr 2
    have hfx : (e₀ ≫ pullback.fst c _).base x₀.1 ∈ 𝒱.U0 := hspec.mem_open 𝒱.U0.2 h0
    rw [CommRingCat.comp_apply]
    erw [← CommRingCat.comp_apply (X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0) (X.presheaf.stalkSpecializes hspec),
      TopCat.Presheaf.germ_stalkSpecializes X.presheaf h0 hspec]
    erw [Scheme.Hom.germ_stalkMap_apply (e₀ ≫ pullback.fst c _) 𝒱.U0 x₀.1 hfx]
    rw [RingHom.algebraMap_toAlgebra]
    erw [← CommRingCat.comp_apply (M₀.C.presheaf.germ _ x₀.1 hfx), TopCat.Presheaf.germ_stalkSpecializes]

  have hΦ1 : ∀ h1 : εinf.1.base s ∈ 𝒱.U1,
      KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR
        (KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := X.presheaf.stalk (εinf.1.base s))
          (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom (hc1 h1) ω.val.2) = res ω := by
    intro h1

    have hξx : genericPoint M₀.C ⤳ x₀.1 := (genericPoint_spec M₀.C).specializes (Set.mem_univ _)
    have hfx1 : (e₀ ≫ pullback.fst c _).base x₀.1 ∈ 𝒱.U1 := hspec.mem_open 𝒱.U1.2 h1
    have hξ1 : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) ∈ 𝒱.U1 :=
      (hξx.map (e₀ ≫ pullback.fst c _).continuous).mem_open 𝒱.U1.2 hfx1
    have hξ01 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) := ⟨hgen0, hξ1⟩
    have hξ1' : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U1 := hξ1

    set BarEmb : ↥(modularFunctionFieldFull N) →+* ↥(modularFunctionFieldBar N) :=
      (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull N))).toRingHom with hBarEmb
    have hBarEmb_val : ∀ z : ↥(modularFunctionFieldFull N), ((BarEmb z : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (z : LaurentSeries ℚ) := by
      intro z
      simp only [hBarEmb, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        AlgEquiv.coe_algHom, Algebra.TensorProduct.includeRight_apply, baseChangeEquiv_one_tmul]
    set E01 : (𝒱.cover c).A01 →+* ↥(modularFunctionFieldBar N) :=
      BarEmb.comp (M₀.ffEquiv.symm.toRingHom.comp ((M₀.C.presheaf.germ _ (genericPoint M₀.C) hξ01).hom.comp
        ((e₀ ≫ pullback.fst c _).app (𝒱.U0 ⊓ 𝒱.U1)).hom)) with hE01

    have hE0 : E01.comp (𝒱.cover c).ρ0.toRingHom = ι := by
      refine RingHom.ext fun a => ?_
      apply Subtype.val_injective
      change ((E01 ((𝒱.cover c).ρ0 a) : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) = ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ))
      rw [hιdef, hE01, RingHom.comp_apply, hBarEmb_val]
      congr 2
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      congr 1
      rw [AlgebraicGeometry.Scheme.TwoAffineOpenCover.cover_ρ0_apply]
      erw [← CommRingCat.comp_apply (X.presheaf.map _) ((e₀ ≫ pullback.fst c _).app (𝒱.U0 ⊓ 𝒱.U1)), Scheme.Hom.naturality]
      rw [CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]

    have hE1 : E01.comp (𝒱.cover c).ρ1.toRingHom =
        Exp.comp ((X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom : (𝒱.cover c).A1 →+* X.presheaf.stalk (εinf.1.base s)) := by
      refine RingHom.ext fun a => ?_
      apply Subtype.val_injective
      change ((E01 ((𝒱.cover c).ρ1 a) : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((Exp ((X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom a) : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ))
      rw [hExpRoute, hE01, RingHom.comp_apply, hBarEmb_val]
      congr 2
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      congr 1

      rw [AlgebraicGeometry.Scheme.TwoAffineOpenCover.cover_ρ1_apply]
      erw [← CommRingCat.comp_apply (X.presheaf.map _) ((e₀ ≫ pullback.fst c _).app (𝒱.U0 ⊓ 𝒱.U1)), Scheme.Hom.naturality]
      rw [CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]
      symm
      rw [CommRingCat.comp_apply]
      erw [← CommRingCat.comp_apply (X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1) (X.presheaf.stalkSpecializes hspec),
        TopCat.Presheaf.germ_stalkSpecializes X.presheaf h1 hspec]
      erw [Scheme.Hom.germ_stalkMap_apply (e₀ ≫ pullback.fst c _) 𝒱.U1 x₀.1 hfx1]
      rw [RingHom.algebraMap_toAlgebra]
      erw [← CommRingCat.comp_apply (M₀.C.presheaf.germ _ x₀.1 hfx1), TopCat.Presheaf.germ_stalkSpecializes]

    have hcoc := ((𝒱.cover c).kaehler.mem_H0_iff ω.val).mp ω.2

    have hE0c : E01.comp (↑(𝒱.cover c).ρ0 : (𝒱.cover c).A0 →+* (𝒱.cover c).A01) = ι := by
      rw [← AlgHom.toRingHom_eq_coe]; exact hE0
    have hE01R : E01.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A01) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
      rw [← (𝒱.cover c).ρ0.comp_algebraMap, ← RingHom.comp_assoc, hE0c]; exact hιR
    have H3' : (E01.comp (𝒱.cover c).ρ1.toRingHom).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A1) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [RingHom.comp_id, RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, (𝒱.cover c).ρ1.comp_algebraMap]; exact hE01R
    have H3 : (Exp.comp ((X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom : (𝒱.cover c).A1 →+* X.presheaf.stalk (εinf.1.base s))).comp
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A1) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [← hE1]; exact H3'
    have H4 : (E01.comp (𝒱.cover c).ρ0.toRingHom).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [hE0, RingHom.comp_id]; exact hιR
    calc KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR
          (KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := X.presheaf.stalk (εinf.1.base s))
            (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom (hc1 h1) ω.val.2)
        = KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := ↥(modularFunctionFieldBar N)) ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)))
            (Exp.comp ((X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom : (𝒱.cover c).A1 →+* X.presheaf.stalk (εinf.1.base s))) H3 ω.val.2 :=
          KaehlerDifferential.mapOfRingHom_comp_apply (A := (𝒱.cover c).A1) (B := X.presheaf.stalk (εinf.1.base s))
            (τ := RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (φ := (X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom) (h := hc1 h1)
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR H3 ω.val.2
      _ = KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := ↥(modularFunctionFieldBar N)) ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)))
            (E01.comp (𝒱.cover c).ρ1.toRingHom) H3' ω.val.2 :=
          KaehlerDifferential.mapOfRingHom_congr (R := ↥(GaloisRep.ratLocalizedAt p)) (S := AlgebraicClosure ℚ) (A := (𝒱.cover c).A1)
            (B := ↥(modularFunctionFieldBar N)) hE1.symm H3 H3' ω.val.2
      _ = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) E01 hE01R ((𝒱.cover c).kaehler.r1 ω.val.2) :=
          (KaehlerDifferential.mapOfRingHom_comp_apply (A := (𝒱.cover c).A1) (B := (𝒱.cover c).A01) (C := ↥(modularFunctionFieldBar N))
            (τ := RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (φ := (𝒱.cover c).ρ1.toRingHom) (h := (𝒱.cover c).ρ1_comp_algebraMap_eq_comp_id)
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) E01 hE01R H3' ω.val.2).symm
      _ = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) E01 hE01R ((𝒱.cover c).kaehler.r0 ω.val.1) := by rw [hcoc]
      _ = KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A0) (B := ↥(modularFunctionFieldBar N)) ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)))
            (E01.comp (𝒱.cover c).ρ0.toRingHom) H4 ω.val.1 :=
          KaehlerDifferential.mapOfRingHom_comp_apply (A := (𝒱.cover c).A0) (B := (𝒱.cover c).A01) (C := ↥(modularFunctionFieldBar N))
            (τ := RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (φ := (𝒱.cover c).ρ0.toRingHom) (h := (𝒱.cover c).ρ0_comp_algebraMap_eq_comp_id)
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) E01 hE01R H4 ω.val.1
      _ = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1 :=
          KaehlerDifferential.mapOfRingHom_congr (R := ↥(GaloisRep.ratLocalizedAt p)) (S := AlgebraicClosure ℚ) (A := (𝒱.cover c).A0)
            (B := ↥(modularFunctionFieldBar N)) hE0 H4 hιR ω.val.1
      _ = res ω := (hres ω).symm
  have hgerm : ∃ η : Ω[X.presheaf.stalk (εinf.1.base s)⁄↥(GaloisRep.ratLocalizedAt p)],
      (∃ h0 : εinf.1.base s ∈ 𝒱.U0, KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A0) (B := X.presheaf.stalk (εinf.1.base s))
          (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom (hc0 h0) ω.val.1 = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • η) ∨
      (∃ h1 : εinf.1.base s ∈ 𝒱.U1, KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := X.presheaf.stalk (εinf.1.base s))
          (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom (hc1 h1) ω.val.2 = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • η) := by
    have hcov : εinf.1.base s ∈ 𝒱.U0 ⊔ 𝒱.U1 := by rw [𝒱.sup_eq_top]; trivial
    rcases (TopologicalSpace.Opens.mem_sup.mp hcov) with h0 | h1
    ·
      have H3 : (Exp.comp ((X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom : (𝒱.cover c).A0 →+* X.presheaf.stalk (εinf.1.base s))).comp
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
          (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp
            ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
        rw [hβ0 h0, RingHom.comp_id]; exact hιR
      have hΦ : KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR
          (KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A0) (B := X.presheaf.stalk (εinf.1.base s))
            (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom (hc0 h0) ω.val.1) = res ω := by
        rw [hres ω, KaehlerDifferential.mapOfRingHom_comp_apply (A := (𝒱.cover c).A0) (B := X.presheaf.stalk (εinf.1.base s))
          (τ := RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (φ := (X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom) (h := hc0 h0)
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR H3]
        exact KaehlerDifferential.mapOfRingHom_congr (R := ↥(GaloisRep.ratLocalizedAt p)) (S := AlgebraicClosure ℚ) (A := (𝒱.cover c).A0)
          (B := ↥(modularFunctionFieldBar N)) (hβ0 h0) H3 hιR ω.val.1
      obtain ⟨η, hη⟩ := key _ hΦ
      exact ⟨η, Or.inl ⟨h0, hη⟩⟩
    ·
      obtain ⟨η, hη⟩ := key _ (hΦ1 h1)
      exact ⟨η, Or.inr ⟨h1, hη⟩⟩

  exact AlgebraicGeometry.exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hmax qκ hker c 𝒱 (εinf.1.base s) hx ω hc0 hc1 hgerm

end S_ModularCurve_exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero (solution)
