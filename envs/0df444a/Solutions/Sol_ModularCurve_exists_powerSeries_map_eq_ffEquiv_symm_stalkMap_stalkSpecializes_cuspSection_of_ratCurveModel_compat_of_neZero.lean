-- Prove2me | solution 1 for ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/521f344f-1758-5dc0-903c-e6dd41f52725

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

import Theorems.Thm_ModularCurve_exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

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
    (z : X.presheaf.stalk (εinf.1.base s)) :
    ∃ P : PowerSeries ↥(GaloisRep.ratLocalizedAt p),
      ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom z))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (P.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
  classical

  obtain ⟨π, t, u, hker, ht, hcot, hu, -, -⟩ :=
    ModularCurve.exists_algHom_retraction_param_stalk_cuspSection_ffEquiv_symm_eq_ofPowerSeries_isUnit_coeff_one_of_ratCurveModel_compat_of_neZero
      N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec

  let ιR : ↥(GaloisRep.ratLocalizedAt p) →+* X.presheaf.stalk (εinf.1.base s) :=
    (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp
      (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) := ιR.toAlgebra
  let f₀ := e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))
  let route : X.presheaf.stalk (εinf.1.base s) →+* M₀.C.presheaf.stalk x₀.1 :=
    (Scheme.Hom.stalkMap f₀ x₀.1).hom.comp (X.presheaf.stalkSpecializes hspec).hom
  have hπι : π.toRingHom.comp ιR = RingHom.id _ := RingHom.ext fun r => π.commutes r

  have hf₀c : f₀ ≫ c = M₀.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
    simp only [f₀, Category.assoc, pullback.condition]
    rw [← Category.assoc, he₀]
  have hι : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
      ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField (route (ιR r))) :
        ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = HahnSeries.C (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r) := by
    intro r

    have h1 : route (ιR r) = (M₀.C.presheaf.germ ⊤ x₀.1 trivial).hom
        (M₀.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r))) := by
      change (Scheme.Hom.stalkMap f₀ x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom
        ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv r)))) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply f₀ ⊤ x₀.1 trivial]
      change (M₀.C.presheaf.germ ⊤ x₀.1 trivial).hom ((c.appTop ≫ f₀.appTop) _) = _
      rw [← Scheme.Hom.comp_appTop, hf₀c, Scheme.Hom.comp_appTop]
      change (M₀.C.presheaf.germ ⊤ x₀.1 trivial).hom (M₀.toBase.appTop
        (((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))).appTop) r)) = _
      rw [← Scheme.ΓSpecIso_inv_naturality]
      rfl
    have h2 : algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField (route (ιR r)) =
        AlgebraicCurve.baseToFunctionField M₀.toBase (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r) := by
      rw [h1]
      change (M₀.C.presheaf.stalkSpecializes _).hom ((M₀.C.presheaf.germ ⊤ x₀.1 trivial).hom _) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      rfl
    rw [h2, ← M₀.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]
    have hC : ∀ (inst : Algebra ℚ ↥(modularFunctionFieldFull N)) (q : ℚ),
        ((@algebraMap ℚ ↥(modularFunctionFieldFull N) _ _ inst q : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
          HahnSeries.C q := by
      intro inst q
      exact RingHom.congr_fun (RingHom.ext_rat
        (((modularFunctionFieldFull N).val : ↥(modularFunctionFieldFull N) →+* LaurentSeries ℚ).comp
          (@algebraMap ℚ ↥(modularFunctionFieldFull N) _ _ inst)) HahnSeries.C) q
    exact hC _ _

  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing (Fact.out : p.Prime)
  have hsmax : s.asIdeal = IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs)
  have hs_closed : s = IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt p) := PrimeSpectrum.ext hsmax
  let σ : X.presheaf.stalk (εinf.1.base s) →+* (Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk s :=
    (Scheme.Hom.stalkMap εinf.1 s).hom
  have hσι : ∀ r : ↥(GaloisRep.ratLocalizedAt p), σ (ιR r) =
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ((Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk s) r := by
    intro r
    change (Scheme.Hom.stalkMap εinf.1 s).hom ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom
      (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv r))) = _
    rw [Scheme.Hom.germ_stalkMap_apply εinf.1 ⊤ s trivial]
    change ((Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ s trivial).hom ((c.appTop ≫ εinf.1.appTop) _) = _
    rw [← Scheme.Hom.comp_appTop, εinf.2]
    rfl
  have hkerπ : ∀ i, π i = 0 → σ i = 0 := by
    intro i hi

    have Hunits : s.asIdeal.primeCompl ≤ IsUnit.submonoid ↥(GaloisRep.ratLocalizedAt p) := by
      intro x hx
      have hx' : x ∉ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) := hsmax ▸ hx
      exact (IsLocalRing.notMem_maximalIdeal.mp hx')
    let E := IsLocalization.atUnits ↥(GaloisRep.ratLocalizedAt p) s.asIdeal.primeCompl
      (S := (Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk s) Hunits
    have hE : ∀ r, E r = algebraMap ↥(GaloisRep.ratLocalizedAt p) ((Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk s) r := fun r => rfl
    let r := E.symm (σ i)
    have h1 : σ (ιR r) = σ i := by rw [hσι, ← hE]; exact AlgEquiv.apply_symm_apply E _
    have h2 : i - ιR r ∈ RingHom.ker (Scheme.Hom.stalkMap εinf.1 s).hom := by
      rw [RingHom.mem_ker, map_sub]; exact sub_eq_zero.mpr h1.symm
    have h3 := hker h2
    rw [RingHom.mem_ker, map_sub, hi, zero_sub, neg_eq_zero] at h3
    have h4 : r = 0 := by simpa using (π.commutes r).symm.trans h3
    have h5 : σ i = E r := (AlgEquiv.apply_symm_apply E _).symm
    rw [h5, h4, map_zero]

  let η' : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) :=
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) (IsLocalRing.closedPoint ℚ)
  have hE1 : f₀ x₀.1 = εinf.1 η' := by
    have h1 : e₀ x₀.1 = y (IsLocalRing.closedPoint ℚ) := by
      rw [← hyx₀, ← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    change (pullback.fst c _) (e₀ x₀.1) = _
    rw [h1, ← Scheme.Hom.comp_apply, hyε, Scheme.Hom.comp_apply]
  have hη's : η' ⤳ s := hs_closed ▸ IsLocalRing.specializes_closedPoint η'
  have h₁ : εinf.1 η' ⤳ εinf.1 s := hη's.map εinf.1.continuous
  have h₂ : f₀ x₀.1 ⤳ εinf.1 η' := hE1 ▸ specializes_rfl
  have h₂' : εinf.1 η' ⤳ f₀ x₀.1 := hE1 ▸ specializes_rfl
  have hI : ∀ i ∈ RingHom.ker π.toRingHom, route i ∈ IsLocalRing.maximalIdeal (M₀.C.presheaf.stalk x₀.1) := by
    intro i hi
    rw [RingHom.mem_ker] at hi
    have hσ0 : σ i = 0 := hkerπ i hi

    have hj : (Scheme.Hom.stalkMap εinf.1 η').hom ((X.presheaf.stalkSpecializes h₁).hom i) = 0 := by
      rw [Scheme.Hom.stalkSpecializes_stalkMap_apply εinf.1 η' s hη's i]
      change ((Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.stalkSpecializes hη's).hom (σ i) = 0
      rw [hσ0]; exact map_zero _
    have hju : ¬ IsUnit ((X.presheaf.stalkSpecializes h₁).hom i) := by
      intro hu
      have := hu.map (Scheme.Hom.stalkMap εinf.1 η').hom
      rw [hj] at this
      exact not_isUnit_zero this

    have hcomp : (X.presheaf.stalkSpecializes hspec).hom i =
        (X.presheaf.stalkSpecializes h₂).hom ((X.presheaf.stalkSpecializes h₁).hom i) := by
      rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    have hinv' : X.presheaf.stalkSpecializes h₂ ≫ X.presheaf.stalkSpecializes h₂' = 𝟙 _ := by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact TopCat.Presheaf.stalkSpecializes_refl _ _
    have hinv : ∀ w, (X.presheaf.stalkSpecializes h₂').hom ((X.presheaf.stalkSpecializes h₂).hom w) = w := fun w =>
      ConcreteCategory.congr_hom hinv' w
    have hspu : ¬ IsUnit ((X.presheaf.stalkSpecializes hspec).hom i) := by
      rw [hcomp]
      intro hu
      apply hju
      have := hu.map (X.presheaf.stalkSpecializes h₂').hom
      rwa [hinv] at this

    have hru : ¬ IsUnit (route i) := fun hu =>
      hspu ((isUnit_map_iff (Scheme.Hom.stalkMap f₀ x₀.1).hom _).mp hu)
    exact (IsLocalRing.mem_maximalIdeal _).mpr hru

  obtain ⟨P, hP, -⟩ := ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
    N M₀ x₀ hx₀ ιR π.toRingHom hπι t ht hcot route hι hI u hu z
  exact ⟨P, hP⟩

end S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero (solution)
