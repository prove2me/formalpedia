-- Prove2me | solution 1 for ModularCurve.exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3125bd90-9d3e-59a5-a6b1-a5fbf52fdf66

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
import Theorems.Thm_CuspForm_mem_intLattice_iff
import Theorems.Thm_ModularCurve_exists_pow_smul_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
import Theorems.Thm_ModularCurve_exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve~coeffMap_injective P2MW.S_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero.ModularCurve AlgebraicCurve IsLocalRing CuspForm"

namespace ModularCurve
p2m_export "ModularCurve" "diffQExpBar arithmeticGalois modularFunctionFieldBar modularFunctionFieldFull coeffMap coeffMap_coeff coeffEmb IsPlaceReductionModL coeffMap_ofPowerSeries modularFunctionFieldFullC baseChangeEquiv cuspInftyFull exists_pow_smul_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero"
namespace OntoN
p2m_open "ModularCurve~coeffMap_injective"

private theorem _root_.PowerSeries.map_map' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (Q : PowerSeries R) : (Q.map f).map g = Q.map (g.comp f) := by
  rw [PowerSeries.map_comp]; rfl

p2m_alias "P2MW.S_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero.PowerSeries.map_map'" "PowerSeries.map_map'"

theorem exists_map_eq_qExpansion {N : ℕ} (f : ↥(CuspForm.intLattice N 2)) :
    ∃ P₀ : PowerSeries ℤ, P₀.map (Int.castRingHom ℂ) =
      UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  have hf := (CuspForm.mem_intLattice_iff (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)).mp f.2
  choose m hm using hf
  refine ⟨PowerSeries.mk m, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact (hm n).symm

theorem eq_ofPowerSeries_smul_of_coeffMap_eq {R K : Type*} [CommRing R] [Field K] (a : R →+* K) (ι₀ : K →+* ℂ)
    (P₀ : PowerSeries ℤ) (p k : ℕ) (L : LaurentSeries K)
    (hL : coeffMap ι₀ L = ((p : ℂ) ^ (k + 1)) • HahnSeries.ofPowerSeries ℤ ℂ (P₀.map (Int.castRingHom ℂ))) :
    L = HahnSeries.ofPowerSeries ℤ K
      ((((p : ℕ) : R) • ((((p : ℕ) : R) ^ k) • P₀.map (Int.castRingHom R))).map a) := by
  have hinj : Function.Injective (coeffMap ι₀) := by
    intro x y h; ext n; exact ι₀.injective (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])
  apply hinj
  rw [hL, ModularCurve.coeffMap_ofPowerSeries, PowerSeries.map_map', smul_smul, ← pow_succ',
    PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, PowerSeries.map_map', map_pow, map_natCast,
    RingHom.ext_int ((ι₀.comp a).comp (Int.castRingHom R)) (Int.castRingHom ℂ), ← PowerSeries.smul_eq_C_mul,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (coeffMap g) := by
  intro x y h
  ext k
  exact hg (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem ofPowerSeries_smul {S : Type*} [CommRing S] (a : S) (Q : PowerSeries S) :
    HahnSeries.ofPowerSeries ℤ S (a • Q) = a • HahnSeries.ofPowerSeries ℤ S Q := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

end ModularCurve.OntoN

set_option maxHeartbeats 3200000 in
open ModularCurve.OntoN in

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
    (f : ↥(CuspForm.intLattice N 2)) :
    ∃ ω : ↥((𝒱.kaehlerSections c).H0),
      coeffMap ι₀ (diffQExpBar N (res ω)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by

  obtain ⟨m, ω, hω⟩ := ModularCurve.exists_pow_smul_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero N p hpN ι₀ c 𝒱 M₀ e₀ he₀ hgen0 ι hιdef hιR res hres εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp f
  set F : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ
    (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) with hF

  obtain ⟨P₀, hP₀⟩ := exists_map_eq_qExpansion f

  have hΦsmul : ∀ ω' : ↥((𝒱.kaehlerSections c).H0),
      coeffMap ι₀ (diffQExpBar N (res (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • ω'))) =
        (p : ℂ) • coeffMap ι₀ (diffQExpBar N (res ω')) := by
    intro ω'
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]

  induction m generalizing ω with
  | zero => exact ⟨ω, by rw [hω, pow_zero, one_smul]⟩
  | succ k ih =>

    have hP := eq_ofPowerSeries_smul_of_coeffMap_eq
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι₀ P₀ p k (diffQExpBar N (res ω))
      (by rw [hω, hF, hP₀])
    obtain ⟨ω', rfl⟩ := ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero N p hpN ι₀ c 𝒱 M₀ e₀ he₀ hgen0 ι hιdef hιR res hres εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp ω _ hP
    refine ih ω' ?_
    have h := hω
    rw [hΦsmul, pow_succ', mul_smul] at h
    exact smul_right_injective (LaurentSeries ℂ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h

end S_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero (solution)
