-- Prove2me | solution 1 for ModularCurve.exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5815e92d-d80a-5dcd-b383-c371d30a4c6d

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
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_notMem_span_germ_and_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_mul_stalkSpecializes_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply"

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

theorem K1e.coe_algebraMap_full (N : ℕ) (q : ℚ) :
    ((algebraMap ℚ ↥(ModularCurve.modularFunctionFieldFull N) q :
      ↥(ModularCurve.modularFunctionFieldFull N)) : LaurentSeries ℚ) = HahnSeries.C q := by
  haveI : CharZero (LaurentSeries ℚ) := algebraRat.charZero _
  haveI : CharZero ↥(ModularCurve.modularFunctionFieldFull N) := algebraRat.charZero _
  rw [eq_ratCast (algebraMap ℚ ↥(ModularCurve.modularFunctionFieldFull N)) q, SubfieldClass.coe_ratCast,
    eq_ratCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) q]

set_option maxHeartbeats 6400000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

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

    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))))
    (hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s)
    :
    letI : Algebra ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) := ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).toAlgebra
    ∃ (π : X.presheaf.stalk (εinf.1.base s) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))
      (t : X.presheaf.stalk (εinf.1.base s)) (u : PowerSeries ↥(GaloisRep.ratLocalizedAt p)),

      RingHom.ker (Scheme.Hom.stalkMap εinf.1 s).hom ≤ RingHom.ker π ∧
      π t = 0 ∧ (RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2) ∧

      ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom t))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ∧
      PowerSeries.constantCoeff u = 0 ∧ IsUnit (PowerSeries.coeff 1 u) := by
  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing (Fact.out : p.Prime)
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) := ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp
      (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).toAlgebra

  obtain ⟨π, t₀, hker, hπt₀, hcot, hfin⟩ := AlgebraicGeometry.exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one c εinf.1 εinf.2 s hs

  obtain ⟨a, b, ha, hb, hab⟩ :=
    ModularCurve.exists_notMem_span_germ_and_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero
      N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  set qκ : ↥(GaloisRep.ratLocalizedAt p) →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp (ρ A hA) with hqκ
  have hmaxR : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p (Fact.out)
  have hkerq : RingHom.ker qκ = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by
    apply le_antisymm
    · rw [← hmaxR]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top qκ)
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hqκ, RingHom.comp_apply, map_natCast,
        IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
      (first | exact hA | simpa using hA | (have h__ := hA; simp at h__; exact h__))
  have hmax : (Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} : Ideal ↥(GaloisRep.ratLocalizedAt p)).IsMaximal := by
    rw [← hmaxR]; exact IsLocalRing.maximalIdeal.isMaximal ↥(GaloisRep.ratLocalizedAt p)
  haveI hes' := hes_iso A hA
  haveI hint : IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom qκ))) := IsIntegral.of_isIso (es A hA)
  have hxfib : εinf.1.base s ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom qκ))).base := by
    have hsq : (Spec.map (CommRingCat.ofHom qκ) ≫ εinf.1) ≫ c = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom qκ) := by
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
      IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hkerq, ← hmaxR]
    exact (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs)).symm
  obtain ⟨hprime, hne⟩ :=
    AlgebraicGeometry.isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hmax qκ hkerq c (εinf.1.base s) hxfib

  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have HGEN : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) = genericPoint X := by
    have hgp : IsGenericPoint ((e₀ ≫ pullback.fst c _).base (genericPoint M₀.C)) Set.univ := by
      rw [isGenericPoint_iff_specializes]
      intro z
      simp only [Set.mem_univ, iff_true]
      rw [specializes_iff_forall_open]
      intro U hU hzU
      exact AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
        (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ) c e₀ ⟨U, hU⟩ ⟨z, hzU⟩
    exact (hgp.inseparable (genericPoint_spec X)).eq
  have hξX : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) ⤳ genericPoint X := HGEN ▸ specializes_rfl
  set Θ : X.functionField →+* ↥(modularFunctionFieldFull N) :=
    M₀.ffEquiv.symm.toRingHom.comp ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M₀.C)).hom.comp
      (X.presheaf.stalkSpecializes hξX).hom) with hΘ
  have hΘinj : Function.Injective Θ := Θ.injective

  have hREAD : ∀ (P : X) (hgenP : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) ⤳ P) (z : X.presheaf.stalk P),
      M₀.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M₀.C)).hom ((X.presheaf.stalkSpecializes hgenP).hom z)) =
        Θ (algebraMap (X.presheaf.stalk P) X.functionField z) := by
    intro P hgenP z
    simp only [hΘ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    congr 2
    rw [RingHom.algebraMap_toAlgebra]
    erw [← CommRingCat.comp_apply (X.presheaf.stalkSpecializes _) (X.presheaf.stalkSpecializes hξX),
      TopCat.Presheaf.stalkSpecializes_comp]

  have hgenInf : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) ⤳ εinf.1.base s :=
    ((genericPoint_specializes x₀.1).map (e₀ ≫ pullback.fst c _).continuous).trans hspec
  have hROUTE : ∀ z : X.presheaf.stalk (εinf.1.base s),
      M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
        ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom z))) =
        Θ (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField z) := by
    intro z
    rw [← hREAD (εinf.1.base s) hgenInf z]
    congr 1
    rw [RingHom.algebraMap_toAlgebra]
    erw [← Scheme.Hom.stalkSpecializes_stalkMap_apply (e₀ ≫ pullback.fst c _) (genericPoint M₀.C) x₀.1 (genericPoint_specializes x₀.1)]
    erw [← CommRingCat.comp_apply (X.presheaf.stalkSpecializes hspec) (X.presheaf.stalkSpecializes _),
      TopCat.Presheaf.stalkSpecializes_comp]

  have hfc : (e₀ ≫ pullback.fst c _) ≫ c = M₀.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he₀]
  have hCONST : ∀ r : ↥(GaloisRep.ratLocalizedAt p), ((Θ (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField
      ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)))) :
        ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = HahnSeries.C (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r) := by
    intro r
    simp only [hΘ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingHom.algebraMap_toAlgebra]
    erw [← CommRingCat.comp_apply (X.presheaf.stalkSpecializes _) (X.presheaf.stalkSpecializes hξX), TopCat.Presheaf.stalkSpecializes_comp]
    erw [← CommRingCat.comp_apply (X.presheaf.germ ⊤ (εinf.1.base s) trivial) (X.presheaf.stalkSpecializes _),
      TopCat.Presheaf.germ_stalkSpecializes]
    erw [Scheme.Hom.germ_stalkMap_apply (e₀ ≫ pullback.fst c _) ⊤ (genericPoint M₀.C) trivial]
    have h3 : (e₀ ≫ pullback.fst c _).appTop.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) =
        M₀.toBase.appTop.hom ((Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) := by
      change (c.appTop ≫ (e₀ ≫ pullback.fst c _).appTop).hom _ = ((Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).appTop ≫ M₀.toBase.appTop).hom _
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hfc]
    have h4 : (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r) := by
      have h := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      rw [← h]
    have h6 : ∀ q : ℚ, M₀.ffEquiv.symm ((M₀.C.presheaf.germ ⊤ (genericPoint M₀.C) trivial).hom
        (M₀.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom q))) =
        algebraMap ℚ ↥(modularFunctionFieldFull N) q := by
      intro q
      apply M₀.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply, M₀.ffEquiv_algebraMap]
      rfl
    erw [h3, h4, h6, K1e.coe_algebraMap_full]

  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  have hNoeth : IsNoetherianRing (X.presheaf.stalk (εinf.1.base s)) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (εinf.1.base s)) isOpen_univ
    obtain ⟨xU, hxUeq⟩ : ∃ xU : U, (xU : X) = εinf.1.base s := ⟨⟨_, hxU⟩, rfl⟩
    haveI := hU.isLocalization_stalk xU
    have hft := HasRingHomProperty.appLE @LocallyOfFiniteType c (inferInstance : LocallyOfFiniteType c)
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    haveI : IsNoetherianRing Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) :=
      isNoetherianRing_of_ringEquiv ↥(GaloisRep.ratLocalizedAt p) (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).symm.commRingCatIsoToRingEquiv
    have hNU : IsNoetherianRing Γ(X, U) := by
      letI := (c.appLE ⊤ U le_top).hom.toAlgebra
      haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) Γ(X, U) := hft
      exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) Γ(X, U)
    rw [← hxUeq]
    exact IsLocalization.isNoetherianRing (hU.primeIdealOf xU).asIdeal.primeCompl _ hNU
  haveI := hNoeth

  have hkerspan : RingHom.ker π = Ideal.span {t₀} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := RingHom.ker π) (IsNoetherian.noetherian _)
      · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
        exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
      · rw [Ideal.smul_eq_mul, ← pow_two]; exact hcot
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; exact hπt₀
  have hϖmax : (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (εinf.1.base s)) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  have hπϖ : π ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := π.commutes ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))
  have ht₀ϖ : t₀ ∉ Ideal.span {(X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))} := by
    intro hmem
    obtain ⟨t₁, ht₁⟩ := Ideal.mem_span_singleton'.mp hmem
    have hπt₁ : π t₁ = 0 := by
      have h := congrArg π ht₁
      rw [map_mul, hπϖ, hπt₀] at h
      exact (mul_eq_zero.mp h).resolve_right (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have ht₁mem : t₁ ∈ Ideal.span {t₀} := hkerspan ▸ (RingHom.mem_ker.mpr hπt₁)
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp ht₁mem
    have hzero : t₀ * (1 - c' * (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) = 0 := by
      rw [mul_sub, mul_one, sub_eq_zero]
      calc t₀ = t₁ * (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) := ht₁.symm
        _ = (c' * t₀) * (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) := by rw [hc']
        _ = t₀ * (c' * (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) := by ring
    have hunit : IsUnit (1 - c' * (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left _ c' hϖmax)
    have ht00 : t₀ = 0 := (hunit.mul_left_eq_zero).mp hzero

    have hkerbot : RingHom.ker π = ⊥ := by rw [hkerspan, ht00, Ideal.span_singleton_eq_bot]
    have hconst : ∀ z : X.presheaf.stalk (εinf.1.base s), z = (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom (π z))) := by
      intro z
      have : z - (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom (π z))) ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        exact (π.commutes (π z)).symm
      rw [hkerbot] at this
      exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)
    have hab' := hab
    rw [hROUTE a, hROUTE b, hconst a, hconst b, hCONST, hCONST] at hab'
    have hπb : π b ≠ 0 := by
      intro h0; apply hb; rw [hconst b, h0, map_zero, map_zero, map_zero]; exact Ideal.zero_mem _
    have hcoef := congrArg (fun w : LaurentSeries ℚ => w.coeff (-1)) hab'
    simp only at hcoef
    rw [mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeff_jq_neg_one, smul_eq_mul, mul_one] at hcoef
    have h0 : (HahnSeries.C ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) (π a)) : LaurentSeries ℚ).coeff (-1) = 0 :=
      HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by norm_num)
    rw [h0] at hcoef
    exact hπb ((map_eq_zero_iff _ (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ)).mp hcoef.symm)

  set K := X.functionField with hK
  have hat₀ : a * t₀ ∉ Ideal.span {(X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))} := by
    intro h
    rcases hprime.mem_or_mem h with h' | h'
    · exact ha h'
    · exact ht₀ϖ h'

  have hREADη : ∀ w : X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1),
      M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
        ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom w)) = Θ (algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField w) := by
    intro w
    rw [← hREAD ((e₀ ≫ pullback.fst c _).base x₀.1) ((genericPoint_specializes x₀.1).map (e₀ ≫ pullback.fst c _).continuous) w]
    congr 1
    rw [RingHom.algebraMap_toAlgebra]
    erw [← Scheme.Hom.stalkSpecializes_stalkMap_apply (e₀ ≫ pullback.fst c _) (genericPoint M₀.C) x₀.1 (genericPoint_specializes x₀.1)]
  have hspecAlg : ∀ {P Q : X} (h : P ⤳ Q) (z : X.presheaf.stalk Q),
      algebraMap (X.presheaf.stalk P) X.functionField ((X.presheaf.stalkSpecializes h).hom z) =
        algebraMap (X.presheaf.stalk Q) X.functionField z := by
    intro P Q h z
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    erw [← CommRingCat.comp_apply (X.presheaf.stalkSpecializes h) (X.presheaf.stalkSpecializes _),
      TopCat.Presheaf.stalkSpecializes_comp]

  have hlocus : ∀ (P : X) (hP : P ⤳ εinf.1.base s),
      IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) →
      P ≠ (e₀ ≫ pullback.fst c _).base x₀.1 → IsUnit ((X.presheaf.stalkSpecializes hP).hom t₀) := by

    have hsmax : s.asIdeal = IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) :=
      IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs)
    have hcε : ∀ t : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), c.base (εinf.1.base t) = t := fun t => by
      have h := congrArg (fun g => g.base t) εinf.2
      (first | exact h | simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h | (have h__ := h; simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h__; exact h__))
    set η₀ : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) := (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).base (IsLocalRing.closedPoint ℚ) with hη₀
    have hη₀bot : η₀.asIdeal = ⊥ := by
      show Ideal.comap (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) (IsLocalRing.closedPoint ℚ).asIdeal = ⊥
      rw [show (IsLocalRing.closedPoint ℚ).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ)
    have hηs : η₀ ⤳ s := (PrimeSpectrum.le_iff_specializes η₀ s).mp (by
      change η₀.asIdeal ≤ s.asIdeal; rw [hη₀bot]; exact bot_le)
    have hPt : (e₀ ≫ pullback.fst c _).base x₀.1 = εinf.1.base η₀ := by
      rw [← hyx₀]
      have h1 : (e₀ ≫ pullback.fst c _).base ((y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ)) =
          ((y ≫ inv e₀) ≫ e₀ ≫ pullback.fst c _).base (IsLocalRing.closedPoint ℚ) := by
        simp only [Scheme.Hom.comp_base, TopCat.comp_app]
      rw [h1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]; rw [hyε]
      simp only [Scheme.Hom.comp_base, TopCat.comp_app]; rfl
    have hyspec : εinf.1.base η₀ ⤳ εinf.1.base s := hηs.map εinf.1.continuous

    have hJ : ∀ z : X.presheaf.stalk (εinf.1.base s), π z = 0 → (εinf.1.stalkMap s).hom z = 0 := by
      intro z hz

      letI algA := (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.algebra_section_stalk (⟨s, trivial⟩ : (⊤ : (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).Opens))
      haveI hls := (isAffineOpen_top (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))).isLocalization_stalk ⟨s, trivial⟩
      have hmaxp := (isAffineOpen_top (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))).primeIdealOf_isMaximal_of_isClosed ⟨s, trivial⟩ hs
      haveI : IsLocalRing Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) :=
        IsLocalRing.of_surjective' (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom
          (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).commRingCatIsoToRingEquiv.symm.surjective
      have hpeq : ((isAffineOpen_top (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))).primeIdealOf ⟨s, trivial⟩).asIdeal =
          IsLocalRing.maximalIdeal Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) := IsLocalRing.eq_maximalIdeal hmaxp
      have hsub : ((isAffineOpen_top (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))).primeIdealOf ⟨s, trivial⟩).asIdeal.primeCompl ≤
          IsUnit.submonoid Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) := by
        intro f hf
        have hf' : f ∉ IsLocalRing.maximalIdeal Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) := hpeq ▸ hf
        exact IsLocalRing.notMem_maximalIdeal.mp hf'
      obtain ⟨a', ha'⟩ := (IsLocalization.atUnits Γ(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)), ⊤) _ (S := (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.stalk s) hsub).surjective
        ((εinf.1.stalkMap s).hom z)
      change ((Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ s trivial).hom a' = (εinf.1.stalkMap s).hom z at ha'
      set r : ↥(GaloisRep.ratLocalizedAt p) := (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).hom.hom a' with hr
      have ha'r : a' = (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r := by
        rw [hr, ← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl

      have hεalg : (εinf.1.stalkMap s).hom ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))) =
          ((Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ s trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r) := by
        erw [Scheme.Hom.germ_stalkMap_apply εinf.1 ⊤ s trivial]
        have happ : εinf.1.appTop.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) =
            (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r := by
          change (c.appTop ≫ εinf.1.appTop).hom _ = _
          rw [← Scheme.Hom.comp_appTop, εinf.2, Scheme.Hom.id_appTop]; rfl
        erw [happ]
        rfl
      have hdiff : z - (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) ∈ RingHom.ker (Scheme.Hom.stalkMap εinf.1 s).hom := by
        rw [RingHom.mem_ker, map_sub, hεalg, ← ha'r, ha', sub_self]
      have hπdiff := hker hdiff
      rw [RingHom.mem_ker, map_sub, hz, zero_sub, neg_eq_zero] at hπdiff
      have hr0 : r = 0 :=
        calc r = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) r := rfl
          _ = π (algebraMap ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) r) := (π.commutes r).symm
          _ = 0 := hπdiff
      rw [← ha', ha'r, hr0, map_zero, map_zero]

    have hpt : ∀ (x' : X) (h : x' ⤳ εinf.1.base s),
        (X.fromSpecStalk (εinf.1.base s)).base
          (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.closedPoint (X.presheaf.stalk x'))) = x' := by
      intro x' h
      have e1 := congrArg (fun g => g.base (IsLocalRing.closedPoint (X.presheaf.stalk x')))
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.fromSpecStalk_closedPoint] at e1
      exact e1

    have hπsurj : Function.Surjective π := fun r => ⟨_, π.commutes r⟩
    have hqker : ∀ 𝔮 : Ideal (X.presheaf.stalk (εinf.1.base s)), 𝔮.IsPrime → RingHom.ker π ≤ 𝔮 → (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) ∉ 𝔮 →
        𝔮 = RingHom.ker π := by
      intro 𝔮 h𝔮 hle hϖ
      apply le_antisymm _ hle
      haveI := h𝔮
      have hmp : (𝔮.map π).IsPrime := Ideal.map_isPrime_of_surjective hπsurj (by simpa using hle)
      by_cases hbot : 𝔮.map π = ⊥
      · intro q hq
        rw [RingHom.mem_ker, ← Ideal.mem_bot, ← hbot]
        exact Ideal.mem_map_of_mem _ hq
      · exfalso
        have hmax' : 𝔮.map π = IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) :=
          IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hbot)
        have hpmem : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ 𝔮.map π := by
          rw [hmax', hmaxR]; exact Ideal.mem_span_singleton_self _
        obtain ⟨q, hq, hπq⟩ := (Ideal.mem_map_iff_of_surjective π hπsurj).mp hpmem
        have : q - (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) ∈ RingHom.ker π := by
          rw [RingHom.mem_ker, map_sub, hπq, hπϖ, sub_self]
        have h2 := hle this
        have : (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) = q - (q - (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) := by ring
        exact hϖ (this ▸ 𝔮.sub_mem hq h2)
    intro P hP hPη hPe

    set 𝔮₀ : Ideal (X.presheaf.stalk (εinf.1.base s)) := Ideal.comap (X.presheaf.stalkSpecializes hP).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk P)) with h𝔮₀
    by_contra hnu
    have ht₀q : t₀ ∈ 𝔮₀ := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hkerle : RingHom.ker π ≤ 𝔮₀ := by rw [hkerspan, Ideal.span_singleton_le_iff_mem]; exact ht₀q
    have hϖP : (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) ∉ 𝔮₀ := by
      intro hmem
      apply (IsLocalRing.mem_maximalIdeal _).mp hmem
      erw [← CommRingCat.comp_apply (X.presheaf.germ ⊤ (εinf.1.base s) trivial) (X.presheaf.stalkSpecializes hP),
        TopCat.Presheaf.germ_stalkSpecializes]
      exact hPη
    have hq0 : 𝔮₀ = RingHom.ker π := hqker 𝔮₀ (Ideal.IsPrime.comap _) hkerle hϖP

    set 𝔮y : Ideal (X.presheaf.stalk (εinf.1.base s)) := Ideal.comap (X.presheaf.stalkSpecializes hyspec).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (εinf.1.base η₀))) with h𝔮y
    have hkerley : RingHom.ker π ≤ 𝔮y := by
      intro z hz
      rw [h𝔮y, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (εinf.1.stalkMap η₀).hom
      erw [Scheme.Hom.stalkSpecializes_stalkMap_apply εinf.1 η₀ s hηs z, hJ z (RingHom.mem_ker.mp hz), map_zero] at hu'
      exact not_isUnit_zero hu'
    have hϖy : (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) ∉ 𝔮y := by
      intro hmem
      apply (IsLocalRing.mem_maximalIdeal _).mp hmem
      erw [← CommRingCat.comp_apply (X.presheaf.germ ⊤ (εinf.1.base s) trivial) (X.presheaf.stalkSpecializes hyspec),
        TopCat.Presheaf.germ_stalkSpecializes]
      erw [← Scheme.Hom.germ_stalkMap_apply c ⊤ (εinf.1.base η₀) trivial]
      refine IsUnit.map _ ?_
      rw [hcε η₀]

      apply (isUnit_map_iff ((Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).stalkMap
        (IsLocalRing.closedPoint ℚ)).hom _).mp
      erw [Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) ⊤
        (IsLocalRing.closedPoint ℚ) trivial]
      have h4 : (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) =
          (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) := by
        have h := congrArg (fun φ => φ.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        rw [← h]
      erw [h4]
      refine IsUnit.map _ (IsUnit.map _ ?_)
      rw [map_natCast]
      exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hqy : 𝔮y = RingHom.ker π := hqker 𝔮y (Ideal.IsPrime.comap _) hkerley hϖy

    apply hPe
    rw [hPt, ← hpt P hP, ← hpt (εinf.1.base η₀) hyspec]
    congr 1
    apply PrimeSpectrum.ext
    change 𝔮₀ = 𝔮y
    rw [hq0, hqy]

  set KX := X.functionField with hKX
  have halginj : Function.Injective (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField) :=
    IsFractionRing.injective (X.presheaf.stalk (εinf.1.base s)) X.functionField
  set α : X.functionField := algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField a with hα
  set β : X.functionField := algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField b with hβ
  set τ : X.functionField := algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField t₀ with hτ
  have ha0 : a ≠ 0 := fun h => ha (h ▸ Ideal.zero_mem _)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ Ideal.zero_mem _)
  have hat0 : a * t₀ ≠ 0 := fun h => hat₀ (h ▸ Ideal.zero_mem _)
  have hα0 : α ≠ 0 := fun h => ha0 (halginj (by rw [map_zero]; exact h))
  have hβ0 : β ≠ 0 := fun h => hb0 (halginj (by rw [map_zero]; exact h))
  have hατ0 : α * τ ≠ 0 := fun h => hat0 (halginj (by rw [map_zero, map_mul]; exact h))
  have hτ0 : τ ≠ 0 := fun h => hατ0 (by rw [h, mul_zero])

  have hcoeinj : Function.Injective (fun w : ↥(modularFunctionFieldFull N) => (w : LaurentSeries ℚ)) := Subtype.val_injective
  have hΘab : ((Θ α : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = (jq : LaurentSeries ℚ) * ((Θ β : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) := by
    rw [hα, hβ, ← hROUTE a, ← hROUTE b]; exact hab
  have hΘβ0 : ((Θ β : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) ≠ 0 := by
    intro h
    apply hβ0
    apply hΘinj
    rw [map_zero]
    exact hcoeinj (by simpa using h)
  have hjq0 : (jq : LaurentSeries ℚ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hΘab
    exact hα0 (hΘinj (by rw [map_zero]; exact hcoeinj (by simpa using hΘab)))
  have hΘdiv : ((Θ (β / α) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = (jq : LaurentSeries ℚ)⁻¹ := by
    rw [map_div₀]
    push_cast
    rw [hΘab]
    field_simp
  set fK : X.functionField := β / (α * τ) with hfK

  have h2 : ∀ P : X, P ⤳ εinf.1.base s →
      IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) →
      fK ∈ Set.range (algebraMap (X.presheaf.stalk P) X.functionField) ∧
        fK⁻¹ ∈ Set.range (algebraMap (X.presheaf.stalk P) X.functionField) := by
    intro P hP hPη
    by_cases hPe : P = (e₀ ≫ pullback.fst c _).base x₀.1
    ·
      subst hPe
      obtain ⟨g, hgu, hg⟩ :=
        ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_mul_stalkSpecializes_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
          N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec
          π.toRingHom (fun r => by exact π.commutes r) hker t₀ hπt₀ hcot
      have hgτ : algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField g * τ = β / α := by
        have h1 : ((Θ (algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField g * τ) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
            (jq : LaurentSeries ℚ)⁻¹ := by
          rw [hτ, ← hspecAlg hspec t₀, ← map_mul, ← hREADη]; exact hg
        rw [← hΘdiv] at h1
        exact hΘinj (hcoeinj h1)
      constructor
      · refine ⟨g, ?_⟩
        rw [hfK, eq_div_iff hατ0, mul_comm α τ, ← mul_assoc, hgτ, div_mul_cancel₀ _ hα0]
      · refine ⟨↑(hgu.unit⁻¹), ?_⟩
        rw [hfK, inv_div, eq_div_iff hβ0]
        have : algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField ↑(hgu.unit⁻¹) *
            algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField g = 1 := by
          rw [← map_mul, IsUnit.val_inv_mul, map_one]
        calc algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField ↑(hgu.unit⁻¹) * β
            = algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField ↑(hgu.unit⁻¹) * β / α * α := by
              rw [div_mul_cancel₀ _ hα0]
          _ = algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField ↑(hgu.unit⁻¹) *
                (algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x₀.1)) X.functionField g * τ) * α := by rw [hgτ, mul_div_assoc]
          _ = α * τ := by rw [← mul_assoc, this, one_mul, mul_comm]
    ·
      have hgenP : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) ⤳ P := HGEN ▸ genericPoint_specializes P
      obtain ⟨g, hgu, hg⟩ :=
        ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero
          N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec P hP hPη hPe hgenP
      have hτu := hlocus P hP hPη hPe
      have hgK : algebraMap (X.presheaf.stalk P) X.functionField g = α / β := by
        have h1 : ((Θ (algebraMap (X.presheaf.stalk P) X.functionField g) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
            (jq : LaurentSeries ℚ) := by rw [← hREAD P hgenP]; exact hg
        have h2 : ((Θ (α / β) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = (jq : LaurentSeries ℚ) := by
          rw [map_div₀]; push_cast; rw [hΘab]; field_simp
        rw [← h2] at h1
        exact hΘinj (hcoeinj h1)
      have hτP : algebraMap (X.presheaf.stalk P) X.functionField ((X.presheaf.stalkSpecializes hP).hom t₀) = τ :=
        hspecAlg hP t₀
      constructor
      · refine ⟨↑(hgu.unit⁻¹) * ↑(hτu.unit⁻¹), ?_⟩
        rw [hfK, eq_div_iff hατ0]
        have e1 : algebraMap (X.presheaf.stalk P) X.functionField ↑(hgu.unit⁻¹) * α = β := by
          have : algebraMap (X.presheaf.stalk P) X.functionField ↑(hgu.unit⁻¹) *
              algebraMap (X.presheaf.stalk P) X.functionField g = 1 := by
            rw [← map_mul, IsUnit.val_inv_mul, map_one]
          calc algebraMap (X.presheaf.stalk P) X.functionField ↑(hgu.unit⁻¹) * α
              = algebraMap (X.presheaf.stalk P) X.functionField ↑(hgu.unit⁻¹) * (α / β) * β := by
                rw [mul_assoc, div_mul_cancel₀ _ hβ0]
            _ = β := by rw [← hgK, this, one_mul]
        have e2 : algebraMap (X.presheaf.stalk P) X.functionField ↑(hτu.unit⁻¹) * τ = 1 := by
          rw [← hτP, ← map_mul, IsUnit.val_inv_mul, map_one]
        calc algebraMap (X.presheaf.stalk P) X.functionField (↑(hgu.unit⁻¹) * ↑(hτu.unit⁻¹)) * (α * τ)
            = (algebraMap (X.presheaf.stalk P) X.functionField ↑(hgu.unit⁻¹) * α) *
                (algebraMap (X.presheaf.stalk P) X.functionField ↑(hτu.unit⁻¹) * τ) := by rw [map_mul]; ring
          _ = β := by rw [e1, e2, mul_one]
      · refine ⟨g * (X.presheaf.stalkSpecializes hP).hom t₀, ?_⟩
        rw [hfK, inv_div, map_mul, hgK, hτP, div_mul_eq_mul_div, div_eq_div_iff hβ0 hβ0]
        try ring
  have hf : ∃ yf : X.presheaf.stalk (εinf.1.base s), IsUnit yf ∧
      algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField (yf * (a * t₀)) = algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField b := by
    obtain ⟨yf, hyf⟩ := AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
      c ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (εinf.1.base s) hprime hne fK
      ⟨b, a * t₀, hat₀, by show β / (α * τ) * algebraMap _ _ (a * t₀) = β; rw [map_mul]; exact div_mul_cancel₀ _ hατ0⟩
      (fun P hP hPη => (h2 P hP hPη).1)
    obtain ⟨yf', hyf'⟩ := AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
      c ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (εinf.1.base s) hprime hne fK⁻¹
      ⟨a * t₀, b, hb, by show (β / (α * τ))⁻¹ * algebraMap _ _ b = algebraMap _ _ (a * t₀); rw [inv_div, map_mul]; exact div_mul_cancel₀ _ hβ0⟩
      (fun P hP hPη => (h2 P hP hPη).2)
    have hfK0 : fK ≠ 0 := div_ne_zero hβ0 hατ0
    refine ⟨yf, isUnit_iff_exists_inv.mpr ⟨yf', halginj ?_⟩, ?_⟩
    · rw [map_mul, hyf, hyf', map_one, mul_inv_cancel₀ hfK0]
    · rw [map_mul, hyf, map_mul]
      exact div_mul_cancel₀ _ hατ0
  obtain ⟨yf, hyfu, hyf⟩ := hf

  have hu : ∃ u : PowerSeries ↥(GaloisRep.ratLocalizedAt p),
      HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) = (jq : LaurentSeries ℚ)⁻¹ ∧
      PowerSeries.constantCoeff u = 0 ∧ IsUnit (PowerSeries.coeff 1 u) := by

    refine ⟨(PowerSeries.X * jNum.invOfUnit 1).map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)), ?_, ?_, ?_⟩
    · have hmap : ((PowerSeries.X * jNum.invOfUnit 1).map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))).map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) =
          (PowerSeries.X * jNum.invOfUnit 1).map (Int.castRingHom ℚ) := by
        change ((PowerSeries.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)).comp (PowerSeries.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)))) _ = _
        rw [← PowerSeries.map_comp]
        congr 1
      rw [hmap]
      have hinv : jNum * jNum.invOfUnit 1 = 1 :=
        PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum]; rfl)
      have h1 : (jq : LaurentSeries ℚ) *
          HahnSeries.ofPowerSeries ℤ ℚ ((PowerSeries.X * jNum.invOfUnit 1).map (Int.castRingHom ℚ)) = 1 := by
        have hjq : (jq : LaurentSeries ℚ) = HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
        have hjNumQ : jNumQ = jNum.map (Int.castRingHom ℚ) := rfl
        rw [hjq, hjNumQ, map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm,
          HahnSeries.single_mul_single, ← map_mul, ← map_mul, hinv, map_one, map_one, mul_one]
        simp
      exact (eq_inv_of_mul_eq_one_right h1)
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X, zero_mul, map_zero]
    · rw [PowerSeries.coeff_map, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
      simp
  obtain ⟨u, hujq, hu0, hu1⟩ := hu

  have hroute : ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom (yf * t₀)))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
    rw [hujq]
    rw [hROUTE, ← hΘdiv]
    congr 2
    rw [map_mul, eq_div_iff hα0]
    calc algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField yf * algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField t₀ * α
        = algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField (yf * (a * t₀)) := by rw [map_mul, map_mul]; ring
      _ = β := hyf

  refine ⟨π, yf * t₀, u, hker, ?_, ?_, hroute, hu0, hu1⟩
  · rw [map_mul, hπt₀, mul_zero]
  ·
    have hspan : Ideal.span {yf * t₀} = Ideal.span {t₀} :=
      Ideal.span_singleton_mul_left_unit hyfu t₀
    rw [hspan]
    exact hcot

end S_ModularCurve_exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero (solution)
