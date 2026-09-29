-- Prove2me | solution 1 for ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9d24e7eb-1a05-55fa-98ec-a7780f93be34

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero
import Theorems.Thm_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials
import Theorems.Thm_ModularCurve_mem_regularDifferentials_of_mem_twoCompRegularDifferentials_of_fst_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve~genusFF"

noncomputable section

namespace RosCountPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace HasValue
private theorem _root_.RosCountPen12.HasValue.add (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hm, hr⟩ := h
  obtain ⟨hm', hr'⟩ := h'
  refine ⟨add_mem hm hm', ?_⟩
  have : (⟨g + g', add_mem hm hm'⟩ : v.toValuationSubring) = ⟨g, hm⟩ + ⟨g', hm'⟩ := Subtype.ext rfl
  rw [this, map_add, hr, hr', map_add]

end HasValue
p2m_export "RosCountPen12" "HasValue.add"
theorem coeff_eq_of_smul_dCoord_eq (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] {f f' : F}
    (h : f • v.dCoord = f' • v.dCoord) : f = f' := by
  have h' : (f - f') • v.dCoord = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 v.dCoord_ne_zero

namespace HasSimpleResidue
private theorem _root_.RosCountPen12.HasSimpleResidue.unique (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} {a b : K}
    (ha : v.HasSimpleResidue ω a) (hb : v.HasSimpleResidue ω b) : a = b := by
  obtain ⟨f, hf, hva⟩ := ha
  obtain ⟨g, hg, hvb⟩ := hb
  have : f = g := coeff_eq_of_smul_dCoord_eq v (hf.symm.trans hg)
  subst this
  exact hva.unique hvb

end HasSimpleResidue
p2m_export "RosCountPen12" "HasSimpleResidue.unique"
namespace HasSimpleResidue
private theorem _root_.RosCountPen12.HasSimpleResidue.add (v : Place K F) {ω η : Ω[F⁄K]} {a b : K}
    (ha : v.HasSimpleResidue ω a) (hb : v.HasSimpleResidue η b) : v.HasSimpleResidue (ω + η) (a + b) := by
  obtain ⟨f, rfl, hva⟩ := ha
  obtain ⟨g, rfl, hvb⟩ := hb
  refine ⟨f + g, by rw [add_smul], ?_⟩
  rw [mul_add]
  exact HasValue.add v hva hvb

end HasSimpleResidue
p2m_export "RosCountPen12" "HasSimpleResidue.add"
theorem HasSimpleResidue.smul (v : Place K F) (c : K) {ω : Ω[F⁄K]} {a : K}
    (ha : v.HasSimpleResidue ω a) : v.HasSimpleResidue (c • ω) (c * a) := by
  obtain ⟨f, rfl, hva⟩ := ha
  refine ⟨algebraMap K F c * f, by rw [← smul_smul, algebraMap_smul], ?_⟩
  rw [mul_left_comm]
  exact (v.hasValue_algebraMap c).mul hva

theorem surjK [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem exists_hasSimpleResidue_of_hasSimplePoleAt [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {ω : Ω[F⁄K]}
    (h : v.HasSimplePoleAt ω) : ∃ a : K, v.HasSimpleResidue ω a := by
  obtain ⟨f, hf, rfl⟩ := h
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective (surjK v) hf
  exact ⟨a, f, rfl, ha⟩

open Classical in

def resAt (v : Place K F) (ω : Ω[F⁄K]) : K :=
  if h : ∃ a : K, v.HasSimpleResidue ω a then h.choose else 0

theorem resAt_spec (v : Place K F) {ω : Ω[F⁄K]} (h : ∃ a : K, v.HasSimpleResidue ω a) :
    v.HasSimpleResidue ω (resAt v ω) := by
  unfold resAt
  rw [dif_pos h]
  exact h.choose_spec

theorem resAt_eq (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} {a : K}
    (ha : v.HasSimpleResidue ω a) : resAt v ω = a :=
  HasSimpleResidue.unique v (resAt_spec v ⟨a, ha⟩) ha

theorem resAt_eq_zero_of_isRegularAt (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]}
    (h : v.IsRegularAt ω) : resAt v ω = 0 := by
  obtain ⟨f, hf, rfl⟩ := h
  exact resAt_eq v (v.hasSimpleResidue_zero_of_mem hf)

theorem isRegularAt_of_hasSimpleResidue_zero (v : Place K F) {ω : Ω[F⁄K]} (h : v.HasSimpleResidue ω 0) :
    v.IsRegularAt ω := by
  obtain ⟨f, rfl, hmem, hres⟩ := h
  refine ⟨f, ?_, rfl⟩

  rw [map_zero] at hres
  have hmax : (⟨v.uniformizer * f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]; exact hres
  have hirr := v.irreducible_mk_uniformizer
  rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hmax
  obtain ⟨g, hg⟩ := hmax
  have hg' : v.uniformizer * f = v.uniformizer * (g : F) := by
    have := congrArg Subtype.val hg
    simpa using this
  have : f = (g : F) := mul_left_cancel₀ v.uniformizer_ne_zero hg'
  rw [this]; exact g.2

section ResMap

variable [IsAlgClosed K] [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]

def resMap (S : Finset (Place K F)) : polarDifferentials K F (S : Set (Place K F)) →ₗ[K] (↥S → K) where
  toFun ω := fun v => resAt v.1 (ω : Ω[F⁄K])
  map_add' ω η := by
    funext v
    have hω := resAt_spec v.1 (exists_hasSimpleResidue_of_hasSimplePoleAt v.1 ((ω.2 v.1).2 (Finset.mem_coe.mpr v.2)))
    have hη := resAt_spec v.1 (exists_hasSimpleResidue_of_hasSimplePoleAt v.1 ((η.2 v.1).2 (Finset.mem_coe.mpr v.2)))
    show resAt v.1 ((ω : Ω[F⁄K]) + (η : Ω[F⁄K])) = resAt v.1 (ω : Ω[F⁄K]) + resAt v.1 (η : Ω[F⁄K])
    exact resAt_eq v.1 (HasSimpleResidue.add v.1 hω hη)
  map_smul' c ω := by
    funext v
    have hω := resAt_spec v.1 (exists_hasSimpleResidue_of_hasSimplePoleAt v.1 ((ω.2 v.1).2 (Finset.mem_coe.mpr v.2)))
    show resAt v.1 (c • (ω : Ω[F⁄K])) = c * resAt v.1 (ω : Ω[F⁄K])
    exact resAt_eq v.1 (HasSimpleResidue.smul v.1 c hω)

theorem resMap_apply (S : Finset (Place K F)) (ω : polarDifferentials K F (S : Set (Place K F))) (v : ↥S) :
    resMap S ω v = resAt v.1 (ω : Ω[F⁄K]) := rfl

theorem mem_ker_resMap_iff (S : Finset (Place K F)) (ω : polarDifferentials K F (S : Set (Place K F))) :
    ω ∈ LinearMap.ker (resMap S) ↔ (ω : Ω[F⁄K]) ∈ regularDifferentials K F := by
  constructor
  · intro h
    have h' : ∀ v : ↥S, resAt v.1 (ω : Ω[F⁄K]) = 0 := fun v => congrFun (LinearMap.mem_ker.mp h) v
    rw [mem_regularDifferentials_iff]
    intro v
    show v.IsRegularAt (ω : Ω[F⁄K])
    by_cases hv : v ∈ (S : Set (Place K F))
    · have hsp := resAt_spec v (exists_hasSimpleResidue_of_hasSimplePoleAt v ((ω.2 v).2 hv))
      rw [h' ⟨v, Finset.mem_coe.mp hv⟩] at hsp
      exact isRegularAt_of_hasSimpleResidue_zero v hsp
    · exact (ω.2 v).1 hv
  · intro h
    rw [LinearMap.mem_ker]
    funext v
    rw [resMap_apply]
    exact resAt_eq_zero_of_isRegularAt v.1 (h v.1)

end ResMap

end RosCountPen12

namespace RosCountPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Dim

variable [IsAlgClosed K] [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]

def sumF (S : Finset (Place K F)) : (↥S → K) →ₗ[K] K where
  toFun a := ∑ v : ↥S, a v
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum]

theorem sumF_apply (S : Finset (Place K F)) (a : ↥S → K) : sumF S a = ∑ v : ↥S, a v := rfl

theorem finrank_ker_sumF (S : Finset (Place K F)) (hS : S.Nonempty) :
    Module.finrank K ↥(LinearMap.ker (sumF S)) + 1 = S.card := by
  classical
  obtain ⟨v₀, hv₀⟩ := hS
  have hsurj : Function.Surjective (sumF S) := by
    intro c
    refine ⟨Pi.single (⟨v₀, hv₀⟩ : ↥S) c, ?_⟩
    rw [sumF_apply, Finset.sum_pi_single']
    simp
  have hrange : Module.finrank K ↥(LinearMap.range (sumF S)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h := LinearMap.finrank_range_add_finrank_ker (sumF S)
  rw [hrange, Module.finrank_pi K, Fintype.card_coe] at h
  omega

variable [Algebra.EssFiniteType K F] [HasCanonicalDivisor (K := K) (F := F)]

theorem range_resMap (S : Finset (Place K F)) : LinearMap.range (resMap S) = LinearMap.ker (sumF S) := by
  classical
  apply le_antisymm
  · rintro _ ⟨ω, rfl⟩
    rw [LinearMap.mem_ker, sumF_apply]
    have ha : ∀ v ∈ S, v.HasSimpleResidue (ω : Ω[F⁄K]) (resAt v (ω : Ω[F⁄K])) := fun v hv =>
      resAt_spec v (exists_hasSimpleResidue_of_hasSimplePoleAt v ((ω.2 v).2 (Finset.mem_coe.mpr hv)))
    have h := AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials S (ω : Ω[F⁄K]) ω.2
      (fun v => resAt v (ω : Ω[F⁄K])) ha
    show ∑ v : ↥S, resAt v.1 (ω : Ω[F⁄K]) = 0
    rw [Finset.sum_coe_sort S (fun v => resAt v (ω : Ω[F⁄K]))]
    exact h
  · intro a ha
    rw [LinearMap.mem_ker, sumF_apply] at ha
    set r : Place K F → K := fun v => if h : v ∈ S then a ⟨v, h⟩ else 0 with hrdef
    have hr : ∑ v ∈ S, r v = 0 := by
      rw [← Finset.sum_coe_sort]
      have : ∀ v : ↥S, r v = a v := fun v => by simp [hrdef, v.2]
      simp_rw [this]
      exact ha
    obtain ⟨ω, hω, hres⟩ := AlgebraicCurve.exists_mem_polarDifferentials_forall_hasSimpleResidue_of_sum_eq_zero S r hr
    refine ⟨⟨ω, hω⟩, ?_⟩
    funext v
    rw [resMap_apply, resAt_eq v.1 (hres v.1 v.2)]
    simp [hrdef, v.2]

def kerResMapEquiv (S : Finset (Place K F)) : ↥(LinearMap.ker (resMap S)) ≃ₗ[K] ↥(regularDifferentials K F) := by
  have heq : LinearMap.ker (resMap S) = (regularDifferentials K F).comap (polarDifferentials K F (S : Set (Place K F))).subtype := by
    ext ω
    rw [mem_ker_resMap_iff, Submodule.mem_comap]
    rfl
  exact (LinearEquiv.ofEq _ _ heq).trans (Submodule.comapSubtypeEquivOfLe (regularDifferentials_le_polarDifferentials _))

theorem finite_and_finrank_polarDifferentials (S : Finset (Place K F)) (hS : S.Nonempty) :
    FiniteDimensional K ↥(polarDifferentials K F (S : Set (Place K F))) ∧
      Module.finrank K ↥(polarDifferentials K F (S : Set (Place K F))) + 1 =
        Module.finrank K ↥(regularDifferentials K F) + S.card := by
  classical
  haveI : Module.Finite K ↥(regularDifferentials K F) :=
    (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)).1
  haveI : Module.Finite K ↥(LinearMap.ker (resMap S)) := Module.Finite.equiv (kerResMapEquiv S).symm
  have hexact : Function.Exact (LinearMap.ker (resMap S)).subtype (resMap S).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  haveI hfin : Module.Finite K ↥(polarDifferentials K F (S : Set (Place K F))) :=
    Module.Finite.of_exact hexact (LinearMap.surjective_rangeRestrict _)
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (resMap S)
  rw [range_resMap, (kerResMapEquiv S).finrank_eq] at h1
  have h2 := finrank_ker_sumF S hS
  omega

end Dim

end RosCountPen12

namespace RosCountPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Glue

variable [IsAlgClosed K] [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]

theorem eq_zero_of_hasSimpleResidue_zero_diff (v : Place K F) {a : K} (h : v.HasSimpleResidue (0 : Ω[F⁄K]) a) : a = 0 := by
  have h0 : v.HasSimpleResidue (0 : Ω[F⁄K]) 0 := by
    have := v.hasSimpleResidue_zero_of_mem (zero_mem v.toValuationSubring)
    rwa [zero_smul] at this
  exact HasSimpleResidue.unique v h h0

theorem eq_zero_of_hasSimpleResidue_of_isRegularAt (v : Place K F) {ω : Ω[F⁄K]} {b : K} (hreg : v.IsRegularAt ω)
    (h : v.HasSimpleResidue ω b) : b = 0 := by
  obtain ⟨f, hf, rfl⟩ := hreg
  exact HasSimpleResidue.unique v h (v.hasSimpleResidue_zero_of_mem hf)

theorem zero_prod_mem_gluedPolarDifferentials (NP : Set (Place K F × Place K F)) {ω₂ : Ω[F⁄K]}
    (h : ω₂ ∈ regularDifferentials K F) : ((0 : Ω[F⁄K]), ω₂) ∈ gluedPolarDifferentials K F NP := by
  refine mem_gluedPolarDifferentials_of_isGluedPolarPair ⟨zero_mem _, regularDifferentials_le_polarDifferentials _ h, ?_⟩
  intro s _ a b ha hb
  rw [eq_zero_of_hasSimpleResidue_zero_diff s.1 ha, eq_zero_of_hasSimpleResidue_of_isRegularAt s.2 (h s.2) hb, add_zero]

end Glue

end RosCountPen12

namespace RosCountPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def fstTo (NP : Set (Place K F × Place K F)) (S : Set (Place K F)) (h : Prod.fst '' NP = S) :
    ↥(gluedPolarDifferentials K F NP) →ₗ[K] ↥(polarDifferentials K F S) :=
  (LinearEquiv.ofEq _ _ (congrArg (polarDifferentials K F) h)).toLinearMap ∘ₗ gluedPolarDifferentials.fst K F NP

theorem coe_fstTo_apply (NP : Set (Place K F × Place K F)) (S : Set (Place K F)) (h : Prod.fst '' NP = S)
    (ω : ↥(gluedPolarDifferentials K F NP)) : (fstTo NP S h ω : Ω[F⁄K]) = (ω : Ω[F⁄K] × Ω[F⁄K]).1 := rfl

end RosCountPen12

end

open RosCountPen12 in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hss : (ModularCurve.ssPlacesQExp K Γ p).Nonempty) :
    FiniteDimensional K ↥(ModularCurve.twoCompRegularDifferentials K Γ p) ∧
      Module.finrank K ↥(ModularCurve.twoCompRegularDifferentials K Γ p) + 1 =
        2 * Module.finrank K ↥(AlgebraicCurve.regularDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ)) +
          Nat.card ↥(ModularCurve.ssNodePairsQExp K Γ p) := by
  classical

  haveI : IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : Algebra.EssFiniteType K ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  haveI : HasCanonicalDivisor (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver

  have hfin : (ModularCurve.ssPlacesQExp K Γ p).Finite := ModularCurve.finite_ssPlacesQExp K p Γ hT
  set S : Finset (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)) := hfin.toFinset with hSdef
  have hScoe : (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) = ModularCurve.ssPlacesQExp K Γ p := hfin.coe_toFinset
  have hSne : S.Nonempty := by
    obtain ⟨v, hv⟩ := hss
    exact ⟨v, hfin.mem_toFinset.mpr hv⟩

  obtain ⟨hPfin, hPdim⟩ := finite_and_finrank_polarDifferentials (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) S hSne

  have hfstNP : Prod.fst '' ModularCurve.ssNodePairsQExp K Γ p = (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) := by
    rw [hScoe, ← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq K p Γ]
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs.1, hs.2.symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(ModularCurve.qExpFrobeniusPlaceModL K Γ p y, y), ⟨hy, rfl⟩, rfl⟩
  have hcardNP : Nat.card ↥(ModularCurve.ssNodePairsQExp K Γ p) = S.card := by
    have e : ↥(ModularCurve.ssNodePairsQExp K Γ p) ≃ ↥(ModularCurve.ssPlacesQExp K Γ p) :=
      { toFun := fun s => ⟨s.1.2, s.2.1⟩
        invFun := fun y => ⟨(ModularCurve.qExpFrobeniusPlaceModL K Γ p y.1, y.1), ModularCurve.frob_mk_mem_ssNodePairsQExp y.2⟩
        left_inv := by
          rintro ⟨⟨a, b⟩, hb, hab⟩
          apply Subtype.ext
          simp only
          exact Prod.ext hab.symm rfl
        right_inv := by rintro ⟨y, hy⟩; rfl }
    rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]

  have hfst_apply : ∀ ω : ↥(ModularCurve.twoCompRegularDifferentials K Γ p), (fstTo (ModularCurve.ssNodePairsQExp K Γ p) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) hfstNP ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]) =
      (ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K] × Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]).1 := fun ω => rfl
  have hsurj : Function.Surjective (fstTo (ModularCurve.ssNodePairsQExp K Γ p) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) hfstNP) := by
    rintro ⟨ω₁, hω₁⟩
    have hω₁' : ω₁ ∈ ModularCurve.ssPolarDifferentials K Γ p := by
      show ω₁ ∈ polarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (ModularCurve.ssPlacesQExp K Γ p)
      rwa [← hScoe]
    obtain ⟨ω₂, h⟩ := ModularCurve.exists_mem_twoCompRegularDifferentials_of_mem_ssPolarDifferentials K p Γ hT ω₁ hω₁'
    exact ⟨⟨(ω₁, ω₂), h⟩, Subtype.ext rfl⟩

  let φ : ↥(LinearMap.ker (fstTo (ModularCurve.ssNodePairsQExp K Γ p) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) hfstNP)) →ₗ[K] ↥(regularDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ)) :=
    { toFun := fun ω => ⟨((ω.1 : ↥(ModularCurve.twoCompRegularDifferentials K Γ p)) : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K] × Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]).2,
        ModularCurve.mem_regularDifferentials_of_mem_twoCompRegularDifferentials_of_fst_eq_zero K p Γ hT _ ω.1.2
          (by have := congrArg Subtype.val (LinearMap.mem_ker.mp ω.2); exact this)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφinj : Function.Injective φ := by
    rintro ⟨⟨ω, hω⟩, hk⟩ ⟨⟨η, hη⟩, hk'⟩ h
    have h2 : ω.2 = η.2 := congrArg Subtype.val h
    have h1 : ω.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    have h1' : η.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hk')
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext (h1.trans h1'.symm) h2
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ω₂, hω₂⟩
    refine ⟨⟨⟨((0 : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]), ω₂), zero_prod_mem_gluedPolarDifferentials _ hω₂⟩, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext rfl
  let eφ : ↥(LinearMap.ker (fstTo (ModularCurve.ssNodePairsQExp K Γ p) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) hfstNP)) ≃ₗ[K] ↥(regularDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ)) := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩

  haveI : Module.Finite K ↥(regularDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ)) :=
    (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ))).1
  haveI : Module.Finite K ↥(LinearMap.ker (fstTo (ModularCurve.ssNodePairsQExp K Γ p) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) hfstNP)) := Module.Finite.equiv eφ.symm
  haveI := hPfin

  have hsndNP : Prod.snd '' ModularCurve.ssNodePairsQExp K Γ p = (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) := by
    rw [hScoe]
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs.1
    · intro hw
      exact ⟨(ModularCurve.qExpFrobeniusPlaceModL K Γ p w, w), ⟨hw, rfl⟩, rfl⟩
  let ψ : ↥(ModularCurve.twoCompRegularDifferentials K Γ p) →ₗ[K] (↥(polarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)))) × ↥(polarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))))) :=
    { toFun := fun ω => (⟨(ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K] × Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]).1, hfstNP ▸ (gluedPolarDifferentials_le_prod _ ω.2).1⟩,
        ⟨(ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K] × Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]).2, hsndNP ▸ (gluedPolarDifferentials_le_prod _ ω.2).2⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := by
    intro ω η h
    have h1 := congrArg (fun z => ((z.1 : ↥(polarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))))) : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K])) h
    have h2 := congrArg (fun z => ((z.2 : ↥(polarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))))) : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K])) h
    apply Subtype.ext
    exact Prod.ext h1 h2
  haveI hVfin : Module.Finite K ↥(ModularCurve.twoCompRegularDifferentials K Γ p) := Module.Finite.of_injective ψ hψ
  haveI : FiniteDimensional K ↥(gluedPolarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (ModularCurve.ssNodePairsQExp K Γ p)) := hVfin
  refine ⟨hVfin, ?_⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (fstTo (ModularCurve.ssNodePairsQExp K Γ p) (S : Set (Place K ↥(ModularCurve.qExpFunctionFieldC K Γ))) hfstNP)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, eφ.finrank_eq] at hrn
  rw [hcardNP]
  show Module.finrank K ↥(gluedPolarDifferentials K ↥(ModularCurve.qExpFunctionFieldC K Γ) (ModularCurve.ssNodePairsQExp K Γ p)) + 1 = _
  omega

end S_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one_eq_two_mul_finrank_regularDifferentials_add_natCard (solution)
