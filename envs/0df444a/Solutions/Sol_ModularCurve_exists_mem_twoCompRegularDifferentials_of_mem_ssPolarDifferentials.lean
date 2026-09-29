-- Prove2me | solution 1 for ModularCurve.exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/db06d50e-4eea-5b07-a1a2-0ff77eff0e03

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
import Theorems.Thm_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

set_option autoImplicit false

noncomputable section

p2m_open "KaehlerDifferential AlgebraicCurve P2MW.S_ModularCurve_exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials.AlgebraicCurve ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place regularDifferentials mem_regularDifferentials_iff polarDifferentials hasSimplePoleAt_of_mem_polarDifferentials regularDifferentials_le_polarDifferentials IsGluedPolarPair gluedPolarDifferentials mem_gluedPolarDifferentials_of_isGluedPolarPair gluedPolarDifferentials_eq_span gluedPolarDifferentials.fst IsCurveOver HasCanonicalDivisor existsUnique_hasSimpleResidue_of_hasSimplePoleAt sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero isCurveOver_of_transcendental_of_perfectField essFiniteType_of_transcendental_of_finiteDimensional hasCanonicalDivisor_of_isCurveOver"
p2m_open "AlgebraicCurve"

namespace FstSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
  [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]

def res (v : Place K F) (ω : Ω[F⁄K]) (h : v.HasSimplePoleAt ω) : K :=
  (existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω h).choose

theorem res_spec (v : Place K F) (ω : Ω[F⁄K]) (h : v.HasSimplePoleAt ω) :
    v.HasSimpleResidue ω (res v ω h) :=
  (existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω h).choose_spec.1

theorem eq_res {v : Place K F} {ω : Ω[F⁄K]} (h : v.HasSimplePoleAt ω) {a : K}
    (ha : v.HasSimpleResidue ω a) : a = res v ω h :=
  (existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω h).unique ha (res_spec v ω h)

theorem exists_isGluedPolarPair (S : Finset (Place K F × Place K F))
    (h₁ : Set.InjOn Prod.fst (S : Set (Place K F × Place K F)))
    (h₂ : Set.InjOn Prod.snd (S : Set (Place K F × Place K F)))
    (ω₁ : Ω[F⁄K]) (hω₁ : ω₁ ∈ polarDifferentials K F (Prod.fst '' (S : Set (Place K F × Place K F)))) :
    ∃ ω₂ : Ω[F⁄K], IsGluedPolarPair K F (S : Set (Place K F × Place K F)) (ω₁, ω₂) := by
  classical

  have hpole : ∀ v : Place K F, v.HasSimplePoleAt ω₁ := hasSimplePoleAt_of_mem_polarDifferentials hω₁
  set r₁ : Place K F → K := fun v => res v ω₁ (hpole v) with hr₁def
  have hr₁ : ∀ v : Place K F, v.HasSimpleResidue ω₁ (r₁ v) := fun v => res_spec v ω₁ (hpole v)

  set T₁ : Finset (Place K F) := S.image Prod.fst with hT₁def
  set T₂ : Finset (Place K F) := S.image Prod.snd with hT₂def
  have hT₁ : (T₁ : Set (Place K F)) = Prod.fst '' (S : Set (Place K F × Place K F)) := Finset.coe_image
  have hT₂ : (T₂ : Set (Place K F)) = Prod.snd '' (S : Set (Place K F × Place K F)) := Finset.coe_image
  have hω₁' : ω₁ ∈ polarDifferentials K F (T₁ : Set (Place K F)) := by rw [hT₁]; exact hω₁

  have hsum₁ : ∑ v ∈ T₁, r₁ v = 0 :=
    sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials T₁ ω₁ hω₁' r₁ fun v _ => hr₁ v

  set r₂ : Place K F → K := fun w => if h : ∃ s ∈ S, s.2 = w then -r₁ h.choose.1 else 0 with hr₂def
  have hr₂ : ∀ s ∈ S, r₂ s.2 = -r₁ s.1 := by
    intro s hs
    have hex : ∃ s' ∈ S, s'.2 = s.2 := ⟨s, hs, rfl⟩
    have hs' := hex.choose_spec
    have heq : hex.choose = s := h₂ hs'.1 hs hs'.2
    show (if h : ∃ s' ∈ S, s'.2 = s.2 then -r₁ h.choose.1 else 0) = -r₁ s.1
    rw [dif_pos hex, heq]
  have hsum₂ : ∑ w ∈ T₂, r₂ w = 0 := by
    rw [Finset.sum_image fun x hx y hy h => h₂ hx hy h]
    rw [Finset.sum_congr rfl fun s hs => hr₂ s hs, Finset.sum_neg_distrib,
      ← Finset.sum_image (f := fun v => r₁ v) fun x hx y hy h => h₁ hx hy h, hsum₁, neg_zero]
  obtain ⟨ω₂, hω₂, hres₂⟩ :=
    exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero T₂ r₂ hsum₂
  refine ⟨ω₂, hω₁, ?_, ?_⟩
  · show ω₂ ∈ polarDifferentials K F (Prod.snd '' (S : Set (Place K F × Place K F)))
    rw [← hT₂]
    exact hω₂
  · intro s hs a b ha hb
    have hsT : s.2 ∈ T₂ := Finset.mem_image_of_mem _ hs
    have ha' : a = r₁ s.1 := eq_res (hpole s.1) ha
    have hb' : b = r₂ s.2 :=
      (eq_res hb.hasSimplePoleAt hb).trans (eq_res hb.hasSimplePoleAt (hres₂ s.2 hsT)).symm
    rw [ha', hb', hr₂ s hs, add_neg_cancel]

theorem fst_surjective (S : Finset (Place K F × Place K F))
    (h₁ : Set.InjOn Prod.fst (S : Set (Place K F × Place K F)))
    (h₂ : Set.InjOn Prod.snd (S : Set (Place K F × Place K F))) :
    Function.Surjective (gluedPolarDifferentials.fst K F (S : Set (Place K F × Place K F))) := by
  rintro ⟨ω₁, hω₁⟩
  obtain ⟨ω₂, hpair⟩ := exists_isGluedPolarPair S h₁ h₂ ω₁ hω₁
  exact ⟨⟨(ω₁, ω₂), mem_gluedPolarDifferentials_of_isGluedPolarPair hpair⟩, rfl⟩

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasSimpleResidue_add {v : Place K F} {ω η : Ω[F⁄K]} {a b : K}
    (hω : v.HasSimpleResidue ω a) (hη : v.HasSimpleResidue η b) : v.HasSimpleResidue (ω + η) (a + b) := by
  obtain ⟨f, rfl, hf⟩ := hω
  obtain ⟨g, rfl, hg⟩ := hη
  refine ⟨f + g, by rw [add_smul], ?_⟩
  rw [mul_add]
  exact hasValue_add hf hg

theorem hasSimpleResidue_smul {v : Place K F} {ω : Ω[F⁄K]} {a : K} (c : K)
    (hω : v.HasSimpleResidue ω a) : v.HasSimpleResidue (c • ω) (c * a) := by
  obtain ⟨f, rfl, hf⟩ := hω
  refine ⟨algebraMap K F c * f, by rw [mul_smul, algebraMap_smul], ?_⟩
  rw [mul_left_comm]
  exact (v.hasValue_algebraMap c).mul hf

theorem hasSimpleResidue_zero (v : Place K F) : v.HasSimpleResidue (0 : Ω[F⁄K]) 0 := by
  have h := v.hasSimpleResidue_zero_of_mem (zero_mem v.toValuationSubring)
  rwa [zero_smul] at h

theorem eq_zero_of_hasSimpleResidue_zero {v : Place K F} {a : K} (h : v.HasSimpleResidue (0 : Ω[F⁄K]) a) :
    a = 0 :=
  (eq_res (v.hasSimplePoleAt_zero) h).trans (eq_res (v.hasSimplePoleAt_zero) (hasSimpleResidue_zero v)).symm

theorem isRegularAt_of_hasSimpleResidue_zero {v : Place K F} {ω : Ω[F⁄K]} (h : v.HasSimpleResidue ω 0) :
    v.IsRegularAt ω := by
  obtain ⟨f, rfl, hm, hres⟩ := h
  refine ⟨f, ?_, rfl⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp v.irreducible_mk_uniformizer,
    Ideal.mem_span_singleton'] at hres
  obtain ⟨g, hg⟩ := hres
  have hgF : (g : F) * v.uniformizer = v.uniformizer * f := by
    have := congrArg (fun x : v.toValuationSubring => (x : F)) hg
    simpa using this
  have hf : f = (g : F) := by
    have h2 : v.uniformizer * f = v.uniformizer * (g : F) := by rw [← hgF, mul_comm]
    exact mul_left_cancel₀ v.uniformizer_ne_zero h2
  rw [hf]
  exact g.2

section Admissible

variable (S : Set (Place K F × Place K F))

theorem isGluedPolarPair_zero : IsGluedPolarPair K F S 0 :=
  ⟨Submodule.zero_mem _, Submodule.zero_mem _, fun s _ a b ha hb => by
    rw [eq_zero_of_hasSimpleResidue_zero ha, eq_zero_of_hasSimpleResidue_zero hb, add_zero]⟩

variable {S}

theorem isGluedPolarPair_add {ω η : Ω[F⁄K] × Ω[F⁄K]} (hω : IsGluedPolarPair K F S ω)
    (hη : IsGluedPolarPair K F S η) : IsGluedPolarPair K F S (ω + η) := by
  obtain ⟨hω1, hω2, hωr⟩ := hω
  obtain ⟨hη1, hη2, hηr⟩ := hη
  refine ⟨Submodule.add_mem _ hω1 hη1, Submodule.add_mem _ hω2 hη2, fun s hs a b ha hb => ?_⟩

  have p1 := hasSimplePoleAt_of_mem_polarDifferentials hω1 s.1
  have p2 := hasSimplePoleAt_of_mem_polarDifferentials hω2 s.2
  have q1 := hasSimplePoleAt_of_mem_polarDifferentials hη1 s.1
  have q2 := hasSimplePoleAt_of_mem_polarDifferentials hη2 s.2

  have ha' : a = res s.1 ω.1 p1 + res s.1 η.1 q1 :=
    (eq_res ha.hasSimplePoleAt ha).trans
      (eq_res ha.hasSimplePoleAt (hasSimpleResidue_add (res_spec s.1 ω.1 p1) (res_spec s.1 η.1 q1))).symm
  have hb' : b = res s.2 ω.2 p2 + res s.2 η.2 q2 :=
    (eq_res hb.hasSimplePoleAt hb).trans
      (eq_res hb.hasSimplePoleAt (hasSimpleResidue_add (res_spec s.2 ω.2 p2) (res_spec s.2 η.2 q2))).symm
  rw [ha', hb', add_add_add_comm, hωr s hs _ _ (res_spec s.1 ω.1 p1) (res_spec s.2 ω.2 p2),
    hηr s hs _ _ (res_spec s.1 η.1 q1) (res_spec s.2 η.2 q2), add_zero]

theorem isGluedPolarPair_smul (c : K) {ω : Ω[F⁄K] × Ω[F⁄K]} (hω : IsGluedPolarPair K F S ω) :
    IsGluedPolarPair K F S (c • ω) := by
  obtain ⟨hω1, hω2, hωr⟩ := hω
  refine ⟨Submodule.smul_mem _ c hω1, Submodule.smul_mem _ c hω2, fun s hs a b ha hb => ?_⟩
  have p1 := hasSimplePoleAt_of_mem_polarDifferentials hω1 s.1
  have p2 := hasSimplePoleAt_of_mem_polarDifferentials hω2 s.2
  have ha' : a = c * res s.1 ω.1 p1 :=
    (eq_res ha.hasSimplePoleAt ha).trans
      (eq_res ha.hasSimplePoleAt (hasSimpleResidue_smul c (res_spec s.1 ω.1 p1))).symm
  have hb' : b = c * res s.2 ω.2 p2 :=
    (eq_res hb.hasSimplePoleAt hb).trans
      (eq_res hb.hasSimplePoleAt (hasSimpleResidue_smul c (res_spec s.2 ω.2 p2))).symm
  rw [ha', hb', ← mul_add, hωr s hs _ _ (res_spec s.1 ω.1 p1) (res_spec s.2 ω.2 p2), mul_zero]

variable (S) in

def admissiblePairs : Submodule K (Ω[F⁄K] × Ω[F⁄K]) where
  carrier := {ω | IsGluedPolarPair K F S ω}
  zero_mem' := isGluedPolarPair_zero S
  add_mem' := isGluedPolarPair_add
  smul_mem' := isGluedPolarPair_smul

variable (S) in

theorem mem_gluedPolarDifferentials_iff (ω : Ω[F⁄K] × Ω[F⁄K]) :
    ω ∈ gluedPolarDifferentials K F S ↔ IsGluedPolarPair K F S ω := by
  constructor
  · intro h
    have hle : gluedPolarDifferentials K F S ≤ admissiblePairs S := by
      rw [gluedPolarDifferentials_eq_span, Submodule.span_le]
      exact fun x hx => hx
    exact hle h
  · exact mem_gluedPolarDifferentials_of_isGluedPolarPair

end Admissible

theorem mem_regularDifferentials_of_mem_gluedPolarDifferentials_of_fst_eq_zero
    (S : Set (Place K F × Place K F)) {ω : Ω[F⁄K] × Ω[F⁄K]} (hω : ω ∈ gluedPolarDifferentials K F S)
    (h0 : ω.1 = 0) : ω.2 ∈ regularDifferentials K F := by
  rw [mem_gluedPolarDifferentials_iff] at hω
  obtain ⟨-, hω2, hr⟩ := hω
  rw [mem_regularDifferentials_iff]
  intro v
  by_cases hv : v ∈ Prod.snd '' S
  · obtain ⟨s, hs, rfl⟩ := hv
    have p2 := hasSimplePoleAt_of_mem_polarDifferentials hω2 s.2
    have hb : res s.2 ω.2 p2 = 0 := by
      have h := hr s hs 0 (res s.2 ω.2 p2) (by rw [h0]; exact hasSimpleResidue_zero s.1) (res_spec s.2 ω.2 p2)
      rwa [zero_add] at h
    have hreg := isRegularAt_of_hasSimpleResidue_zero (hb ▸ res_spec s.2 ω.2 p2)
    obtain ⟨g, hg, hωg⟩ := hreg
    exact ⟨g, hg, hωg⟩
  · obtain ⟨g, hg, hωg⟩ := (hω2 v).1 hv
    exact ⟨g, hg, hωg⟩

theorem fst_eq_zero_iff (S : Set (Place K F × Place K F)) (ω : gluedPolarDifferentials K F S) :
    gluedPolarDifferentials.fst K F S ω = 0 ↔
      (ω : Ω[F⁄K] × Ω[F⁄K]).1 = 0 ∧ (ω : Ω[F⁄K] × Ω[F⁄K]).2 ∈ regularDifferentials K F := by
  constructor
  · intro h
    have h0 : (ω : Ω[F⁄K] × Ω[F⁄K]).1 = 0 := by
      have := congrArg (fun x : polarDifferentials K F (Prod.fst '' S) => (x : Ω[F⁄K])) h
      simpa using this
    exact ⟨h0, mem_regularDifferentials_of_mem_gluedPolarDifferentials_of_fst_eq_zero S ω.2 h0⟩
  · rintro ⟨h0, -⟩
    exact Subtype.ext h0

theorem zero_prod_mem_gluedPolarDifferentials (S : Set (Place K F × Place K F)) {ω₂ : Ω[F⁄K]}
    (h : ω₂ ∈ regularDifferentials K F) : ((0 : Ω[F⁄K]), ω₂) ∈ gluedPolarDifferentials K F S := by
  refine mem_gluedPolarDifferentials_of_isGluedPolarPair ⟨Submodule.zero_mem _,
    regularDifferentials_le_polarDifferentials _ h, fun s hs a b ha hb => ?_⟩
  rw [eq_zero_of_hasSimpleResidue_zero ha, zero_add]
  obtain ⟨g, hg, hωg⟩ := (mem_regularDifferentials_iff.mp h) s.2
  exact (eq_res hb.hasSimplePoleAt hb).trans
    (eq_res hb.hasSimplePoleAt (hωg ▸ s.2.hasSimpleResidue_zero_of_mem hg)).symm

end FstSurj

end AlgebraicCurve

end

open KaehlerDifferential _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials.AlgebraicCurve ModularCurve in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (ω₁ : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hω₁ : ω₁ ∈ ModularCurve.ssPolarDifferentials K Γ p) :
    ∃ ω₂ : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K],
      (ω₁, ω₂) ∈ ModularCurve.twoCompRegularDifferentials K Γ p := by
  classical
  obtain ⟨x, -, hxt, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : IsCurveOver K (ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hfd
  haveI : Algebra.EssFiniteType K (ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxt hfd
  haveI : HasCanonicalDivisor (K := K) (F := ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

  have hfin : (ModularCurve.ssPlacesQExp K Γ p).Finite := ModularCurve.finite_ssPlacesQExp K p Γ hT
  let S : Finset (Place K (ModularCurve.qExpFunctionFieldC K Γ) × Place K (ModularCurve.qExpFunctionFieldC K Γ)) :=
    hfin.toFinset.image fun y => (ModularCurve.qExpFrobeniusPlaceModL K Γ p y, y)
  have hS : (S : Set (Place K (ModularCurve.qExpFunctionFieldC K Γ) × Place K (ModularCurve.qExpFunctionFieldC K Γ))) =
      ModularCurve.ssNodePairsQExp K Γ p := by
    ext s
    simp only [S, Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image, ModularCurve.mem_ssNodePairsQExp_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · rintro ⟨h2, h1⟩
      exact ⟨s.2, h2, Prod.ext h1.symm rfl⟩
  have h₁ : Set.InjOn Prod.fst (S : Set (Place K (ModularCurve.qExpFunctionFieldC K Γ) × Place K (ModularCurve.qExpFunctionFieldC K Γ))) := by
    intro s hs s' hs' h
    rw [hS] at hs hs'
    obtain ⟨-, e⟩ := hs
    obtain ⟨-, e'⟩ := hs'
    have h22 : s.2 = s'.2 :=
      (ModularCurve.qExpFrobeniusPlaceModL_bijective K p Γ).1 (by rw [← e, ← e']; exact h)
    exact Prod.ext h h22
  have h₂ : Set.InjOn Prod.snd (S : Set (Place K (ModularCurve.qExpFunctionFieldC K Γ) × Place K (ModularCurve.qExpFunctionFieldC K Γ))) := by
    intro s hs s' hs' h
    rw [hS] at hs hs'
    obtain ⟨-, e⟩ := hs
    obtain ⟨-, e'⟩ := hs'
    refine Prod.ext ?_ h
    rw [e, e']
    exact congrArg _ h
  have hfst : Prod.fst '' (S : Set (Place K (ModularCurve.qExpFunctionFieldC K Γ) × Place K (ModularCurve.qExpFunctionFieldC K Γ))) = ModularCurve.ssPlacesQExp K Γ p := by
    rw [hS]
    ext w
    simp only [Set.mem_image, ModularCurve.mem_ssNodePairsQExp_iff]
    constructor
    · rintro ⟨s, ⟨h2, h1⟩, rfl⟩
      rw [h1, ← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq K p Γ]
      exact ⟨s.2, h2, rfl⟩
    · intro hw
      rw [← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq K p Γ] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      exact ⟨(ModularCurve.qExpFrobeniusPlaceModL K Γ p y, y), ⟨hy, rfl⟩, rfl⟩
  have hω₁' : ω₁ ∈ polarDifferentials K (ModularCurve.qExpFunctionFieldC K Γ) (Prod.fst '' (S : Set (Place K (ModularCurve.qExpFunctionFieldC K Γ) × Place K (ModularCurve.qExpFunctionFieldC K Γ)))) := by
    rw [hfst]
    exact hω₁
  obtain ⟨ω₂, hpair⟩ := AlgebraicCurve.FstSurj.exists_isGluedPolarPair S h₁ h₂ ω₁ hω₁'
  refine ⟨ω₂, ?_⟩
  show (ω₁, ω₂) ∈ gluedPolarDifferentials K (ModularCurve.qExpFunctionFieldC K Γ) (ModularCurve.ssNodePairsQExp K Γ p)
  rw [← hS]
  exact mem_gluedPolarDifferentials_of_isGluedPolarPair hpair

#print axioms solution

end S_ModularCurve_exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials
end P2MW
export P2MW.S_ModularCurve_exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials (solution)
