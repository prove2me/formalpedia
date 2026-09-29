-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/cc4f7943-1323-507a-8c68-f5208fdface2

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le
import Theorems.Thm_GaloisRep_exists_ideal_le_comap_includeRight_eq_of_natCast_mem
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

namespace Ws49DictInf
namespace Geo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

universe u
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
variable (κ : Type u) [CommRing κ] [Algebra R κ]

abbrev fib : Scheme.{u} := pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))

theorem chart_comm_inf :
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom) ≫ ιInf R F j) ≫
        toBase R F j =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgInf R F j)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
  rw [Category.assoc, ιInf_toBase, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def cInf : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgInf R F j))) ⟶ fib R F j κ := pullback.lift _ _ (chart_comm_inf R F j κ)

@[scoped simp] theorem cInf_fst : cInf R F j κ ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom) ≫ ιInf R F j :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem cInf_snd : cInf R F j κ ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := ↥(chartAlgInf R F j)))) :=
  pullback.lift_snd _ _ _

theorem isPullback_cInf :
    IsPullback (cInf R F j κ) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom))
      (pullback.fst _ _) (ιInf R F j) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap R κ)))
    (h₂₂ := toBase R F j) ?_ (cInf_fst R F j κ) (IsPullback.of_hasPullback _ _).flip
  rw [cInf_snd, ιInf_toBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ ↥(chartAlgInf R F j))

scoped instance isOpenImmersion_cInf : IsOpenImmersion (cInf R F j κ) := by
  rw [← (isPullback_cInf R F j κ).isoPullback_hom_fst]; infer_instance

theorem mem_range_cInf_iff (x : ↥(fib R F j κ)) :
    x ∈ Set.range (cInf R F j κ) ↔ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) x ∈ Set.range (ιInf R F j) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, cInf_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hx
    have H := isPullback_cInf R F j κ
    have hx' : x ∈ Set.range (pullback.fst (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) (ιInf R F j)) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨t, rfl⟩ := hx'
    exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

theorem specializes_of_cInf {x y : PrimeSpectrum (κ ⊗[R] ↥(chartAlgInf R F j))} (h : cInf R F j κ x ⤳ cInf R F j κ y) : x ≤ y :=
  (PrimeSpectrum.le_iff_specializes x y).mpr ((cInf R F j κ).isOpenEmbedding.isInducing.specializes_iff.mp h)

end Ws49DictInf.Geo
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf"

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

namespace Ws49DictInf
namespace KerMin

variable (p : ℕ) [Fact p.Prime]

scoped instance instDVR_R : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

theorem maximalIdeal_R : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out

theorem mem_maximalIdeal_iff_mem_span (a : ↥(GaloisRep.ratLocalizedAt p)) :
    a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) ↔ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by rw [maximalIdeal_R]

theorem p_ne_zero_R : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem irreducible_p : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (p_ne_zero_R p) (maximalIdeal_R p)

theorem prime_p : Prime ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := (irreducible_p p).prime

theorem res_eq_zero_iff (r : ↥(GaloisRep.ratLocalizedAt p)) : GaloisRep.ratLocalizedAtResidue p r = 0 ↔ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ r := by
  rw [← Ideal.mem_span_singleton, ← maximalIdeal_R]
  constructor
  · intro hr
    by_contra h
    have hu : IsUnit r := by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
    exact (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  · intro hr
    rw [maximalIdeal_R, Ideal.mem_span_singleton] at hr
    obtain ⟨t, rfl⟩ := hr
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem residue_eq_zero_iff' (r : ↥(GaloisRep.ratLocalizedAt p)) :
    IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p) r = 0 ↔ GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, res_eq_zero_iff, ← Ideal.mem_span_singleton, maximalIdeal_R]

theorem map_residue_ne_zero_iff (Q : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 ↔ Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩ <;> ext n <;> have hn := congrArg (fun P : Polynomial _ => P.coeff n) h <;>
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn ⊢
  · exact (residue_eq_zero_iff' p _).mp hn
  · exact (residue_eq_zero_iff' p _).mpr hn

theorem map_ne_zero_iff_not_C_dvd (Q : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ↔ ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ Q) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  refine not_congr ⟨fun h n => (res_eq_zero_iff p _).mp ?_, fun h => ?_⟩
  · have hn := congrArg (fun P : Polynomial _ => P.coeff n) h
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hn
  · ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (res_eq_zero_iff p _).mpr (h n)

scoped instance instIsFractionRing_R : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

theorem ringHom_ext_R {S : Type*} [Semiring S] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem isScalarTower_R (Γ : Subgroup SL(2, ℤ)) (inst : Algebra ℚ ↥(qExpFunctionFieldC ℚ Γ)) :
    @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ (@Algebra.toSMul _ _ _ _ inst) _ :=
  @IsScalarTower.of_algebraMap_eq ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ _ _ inst _ fun a =>
    RingHom.congr_fun (ringHom_ext_R p (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ))
      ((@algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ inst).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) a

scoped instance instIsScalarTower (Γ : Subgroup SL(2, ℤ)) : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) :=
  isScalarTower_R p Γ inferInstance

theorem coeffEmb_rat (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext k
  rw [coeffEmb_coeff]
  rfl

theorem coe_jAt_eq_coeffEmb (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
  rw [coeffEmb_rat, coe_jAt]
  rfl

theorem transcendental_iff_of_inst (Γ : Subgroup SL(2, ℤ)) (i₁ i₂ : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ))
    (x : ↥(qExpFunctionFieldC ℚ Γ)) :
    @Transcendental ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₁ x ↔
      @Transcendental ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₂ x := by
  have h : @algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₁ =
      @algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _ _ i₂ := ringHom_ext_R p _ _
  unfold Transcendental IsAlgebraic
  refine not_congr ⟨?_, ?_⟩ <;> rintro ⟨q, hq, hx⟩ <;> refine ⟨q, hq, ?_⟩
  · rw [@Polynomial.aeval_def _ _ _ _ i₂, ← h, ← @Polynomial.aeval_def _ _ _ _ i₁]; exact hx
  · rw [@Polynomial.aeval_def _ _ _ _ i₁, h, ← @Polynomial.aeval_def _ _ _ _ i₂]; exact hx

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra in"

theorem transcendental_jAt_IF (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Transcendental ↥(GaloisRep.ratLocalizedAt p) (jAt Γ hj) := by
  have hst := IsScalarTower.of_algebraMap_eq (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ℚ)
    (A := ↥(qExpFunctionFieldC ℚ Γ)) (fun _ => rfl)
  exact @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ Γ) ↥(GaloisRep.ratLocalizedAt p)
    _ _ _ _ _ hst (jAt Γ hj) (coe_jAt_eq_coeffEmb Γ hj)

theorem transcendental_jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Transcendental ↥(GaloisRep.ratLocalizedAt p) (jAt Γ hj) :=
  (transcendental_iff_of_inst p Γ _ _ _).mp (transcendental_jAt_IF p Γ hj)

theorem finiteDimensional_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) ↥(qExpFunctionFieldC ℚ Γ) := by

  have h := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT Γ le_rfl
    (fun γ hγ => Or.inl hγ) (jAt Γ hj) (coe_jAt Γ hj)).1
  convert h <;> exact Subsingleton.elim _ _

theorem isSeparable_adjoin_jAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt Γ hj} : Set ↥(qExpFunctionFieldC ℚ Γ))) ↥(qExpFunctionFieldC ℚ Γ) := by
  haveI := finiteDimensional_adjoin_jAt Γ hT hj
  infer_instance

end Ws49DictInf.KerMin
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo"

namespace Ws49DictInf
namespace MultOne

variable (p : ℕ) [Fact p.Prime]

theorem gamma1_le_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro γ hγ
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem M γ).mp hγ
  refine CohCarrier.mem_GammaH_iff.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
    Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
  rw [h1]
  exact Subgroup.one_mem _

theorem T_mem_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  gamma1_le_gammaH M H (by rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])

scoped instance finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 M
  exact Subgroup.finiteIndex_of_le (gamma1_le_gammaH M H)

theorem C_dvd_reverse_iff {R : Type*} [CommRing R] (ϖ : R) (Q : Polynomial R) :
    Polynomial.C ϖ ∣ Q.reverse ↔ Polynomial.C ϖ ∣ Q := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h n
    by_cases hn : n ≤ Q.natDegree
    · have := h (Polynomial.revAt Q.natDegree n)
      rwa [Polynomial.coeff_reverse, Polynomial.revAt_invol] at this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
      exact dvd_zero _
  · intro h n
    rw [Polynomial.coeff_reverse]
    exact h _

theorem aeval_mem_of_aeval_inv_mem {R F : Type*} [CommRing R] [Field F] [Algebra R F] (j : F) (hj : j ≠ 0) (ϖ : R)
    (V : ValuationSubring F)
    (hV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V)
    (hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R))) :
    ∀ Q : Polynomial R, ¬ (Polynomial.C ϖ ∣ Q) → Polynomial.aeval j Q ∈ V ∧ (Polynomial.aeval j Q)⁻¹ ∈ V := by
  intro Q hQ
  obtain ⟨hjinv, hj'⟩ := hV Polynomial.X hX
  rw [Polynomial.aeval_X] at hjinv hj'
  rw [inv_inv] at hj'
  obtain ⟨h1, h2⟩ := hV Q.reverse ((C_dvd_reverse_iff ϖ Q).not.mpr hQ)
  letI : Invertible j := invertibleOfNonzero hj
  have e : Polynomial.aeval j Q = Polynomial.aeval j⁻¹ Q.reverse * j ^ Q.natDegree := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← invOf_eq_inv, Polynomial.eval₂_reverse_mul_pow]
  refine ⟨?_, ?_⟩
  · rw [e]; exact mul_mem h1 (pow_mem hj' _)
  · rw [e, mul_inv, ← inv_pow]; exact mul_mem h2 (pow_mem hjinv _)

end Ws49DictInf.MultOne
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.MultOne"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin"

namespace Ws49DictInf
namespace KerMin

variable (p : ℕ) [Fact p.Prime]

universe u in

theorem kerMin_inf_of_pair
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({jAt (CohCarrier.GammaH M H) hj} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW1 : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits)
    (hW2 : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i))
    (hW3 : W₀ ≠ W₁)
    (hW5 : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁) :
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      (∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits)) ∧
    (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))}).minimalPrimes,
      ∀ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), b ∈ 𝔭 ↔ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ (![W₀, W₁] i).nonunits) ∧
    (∃ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₀.nonunits ∧ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₁.nonunits) ∧
    (∃ b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj), ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ W₁.nonunits ∧ ((b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∉ W₀.nonunits) := by
  classical
  have hj0 : (jAt (CohCarrier.GammaH M H) hj) ≠ 0 := Fact.out
  haveI hfact : Fact ((jAt (CohCarrier.GammaH M H) hj)⁻¹ ≠ 0) := ⟨inv_ne_zero hj0⟩
  have htj := transcendental_jAt p (CohCarrier.GammaH M H) hj
  have htj' : Transcendental ↥(GaloisRep.ratLocalizedAt p) ((jAt (CohCarrier.GammaH M H) hj))⁻¹ := fun h => htj (by simpa using h.inv)
  have hadj : IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      IntermediateField.adjoin ℚ ({(jAt (CohCarrier.GammaH M H) hj)} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ((jAt (CohCarrier.GammaH M H) hj)⁻¹))
      rwa [inv_inv] at h
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({((jAt (CohCarrier.GammaH M H) hj))⁻¹} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [hadj]; exact hsep
  have hprime := prime_p p
  have hX : ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ (Polynomial.X : Polynomial ↥(GaloisRep.ratLocalizedAt p))) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro h
    have := h 1
    rw [Polynomial.coeff_X_one] at this
    exact hprime.not_unit (isUnit_of_dvd_one this)
  have hbr : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p),
      Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 ↔ ¬ (Polynomial.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ Q) :=
    fun Q => (map_residue_ne_zero_iff p Q).trans (map_ne_zero_iff_not_C_dvd p Q)
  have h1' : ∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits :=
    fun i => ⟨(hW1 i).1, fun a ha => (hW1 i).2 a ((mem_maximalIdeal_iff_mem_span p a).mp ha)⟩
  have h2' : ∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
      Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q)⁻¹ ∈ (![W₀, W₁] i) := by
    intro i Q hQ
    refine Ws49DictInf.MultOne.aeval_mem_of_aeval_inv_mem ((jAt (CohCarrier.GammaH M H) hj))⁻¹ (inv_ne_zero hj0)
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (![W₀, W₁] i) ?_ hX Q ((hbr Q).mp hQ)
    intro P hP
    rw [inv_inv]
    exact hW2 i P ((map_ne_zero_iff_not_C_dvd p P).mpr hP)
  have h5' : ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V) →
      (∀ a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a ∈ V.nonunits) →
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 →
        Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q ∈ V ∧ (Polynomial.aeval ((jAt (CohCarrier.GammaH M H) hj))⁻¹ Q)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ := by
    intro V hV1 hV1' hV2
    refine hW5 V hV1 (fun a ha => hV1' a ((mem_maximalIdeal_iff_mem_span p a).mpr ha)) ?_
    intro Q hQ
    exact Ws49DictInf.MultOne.aeval_mem_of_aeval_inv_mem (jAt (CohCarrier.GammaH M H) hj) hj0
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) V (fun P hP => hV2 P ((hbr P).mpr hP)) hX Q
      ((map_ne_zero_iff_not_C_dvd p Q).mp hQ)
  haveI := hFD'; haveI := hsep'
  haveI := instIsScalarTower p (CohCarrier.GammaH M H)
  have hϖ : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt p)
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((jAt (CohCarrier.GammaH M H) hj))⁻¹)
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} = Ideal.span {((p : ℕ) : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj))} := by
    rw [map_natCast]
  obtain ⟨hi, hii, hiii⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((jAt (CohCarrier.GammaH M H) hj))⁻¹ htj' hFD' hsep'
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (maximalIdeal_R p) W₀ W₁ h1' h2' hW3 h5'
  rw [hϖ] at hi hii
  exact ⟨hi, hii, hiii⟩

end Ws49DictInf.KerMin
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.MultOne"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.MultOne"

namespace Ws49DictInf
namespace Red

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem exists_lift (b : ↥(chartAlgInf p Γ hj)) :
    ∃ y : LaurentSeries (R p), coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) :=
  (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p (jAt Γ hj) (coe_jAt Γ hj)).2 b

private def _root_.Ws49DictInf.Red.lift (b : ↥(chartAlgInf p Γ hj)) : LaurentSeries (R p) := Classical.choose (exists_lift p Γ hj b)

p2m_export "Ws49DictInf.Red" "lift"
theorem coeffMap_lift (b : ↥(chartAlgInf p Γ hj)) :
    coeffMap (algebraMap (R p) ℚ) (lift p Γ hj b) = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) :=
  Classical.choose_spec (exists_lift p Γ hj b)

theorem coeffMap_rat_injective : Function.Injective (coeffMap (algebraMap (R p) ℚ)) := by
  intro x y h
  haveI := Ws49DictInf.KerMin.instIsFractionRing_R p
  refine HahnSeries.ext ?_
  funext k
  have hk := congrArg (fun s : LaurentSeries ℚ => s.coeff k) h
  simp only [coeffMap_coeff] at hk
  exact IsFractionRing.injective (R p) ℚ hk

variable {p Γ hj} in
theorem lift_eq {b : ↥(chartAlgInf p Γ hj)} {y : LaurentSeries (R p)}
    (h : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) : lift p Γ hj b = y :=
  coeffMap_rat_injective p ((coeffMap_lift p Γ hj b).trans h.symm)

theorem coeffMap_ofPowerSeries' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A q) = HahnSeries.ofPowerSeries ℤ B (q.map f) := by
  ext k
  rw [coeffMap_coeff]
  change f (((q : PowerSeries A) : LaurentSeries A).coeff k) = ((q.map f : PowerSeries B) : LaurentSeries B).coeff k
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · exact (PowerSeries.coeff_map _ _ _).symm

variable {κ : Type} [CommRing κ] (toκ : R p →+* κ)

def red : ↥(chartAlgInf p Γ hj) →+* LaurentSeries κ where
  toFun b := coeffMap toκ (lift p Γ hj b)
  map_one' := by
    rw [lift_eq (y := 1) (by simp only [map_one, OneMemClass.coe_one]), map_one]
  map_mul' a b := by
    rw [lift_eq (y := lift p Γ hj a * lift p Γ hj b)
      (by simp only [map_mul, coeffMap_lift, MulMemClass.coe_mul]), map_mul]
  map_zero' := by
    rw [lift_eq (y := 0) (by simp only [map_zero, ZeroMemClass.coe_zero]), map_zero]
  map_add' a b := by
    rw [lift_eq (y := lift p Γ hj a + lift p Γ hj b)
      (by simp only [map_add, coeffMap_lift, AddMemClass.coe_add]), map_add]

theorem red_apply (b : ↥(chartAlgInf p Γ hj)) : red p Γ hj toκ b = coeffMap toκ (lift p Γ hj b) := rfl

theorem red_eq_of_coeffMap_eq (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p))
    (h : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) :
    red p Γ hj toκ b = coeffMap toκ y := by
  rw [red_apply, lift_eq h]

theorem coe_mem_nonunits_of_red_eq_zero [Nontrivial κ]
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hOW : ∀ b : ↥(chartAlgInf p Γ hj), ((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀)
    (b : ↥(chartAlgInf p Γ hj)) (hb : red p Γ hj toκ b = 0) :
    ((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀.nonunits := by
  classical
  haveI := Ws49DictInf.KerMin.instDVR_R p
  set y := lift p Γ hj b with hydef
  have hyb : coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) :=
    coeffMap_lift p Γ hj b

  have hres : coeffMap (GaloisRep.ratLocalizedAtResidue p) y = 0 := by
    ext k
    rw [coeffMap_coeff, HahnSeries.coeff_zero]
    have hk : toκ (y.coeff k) = 0 := by
      have := congrArg (fun s : LaurentSeries κ => s.coeff k) hb
      simpa only [red_apply, coeffMap_coeff, HahnSeries.coeff_zero] using this
    have hmem : y.coeff k ∈ IsLocalRing.maximalIdeal (R p) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top toκ) ((RingHom.mem_ker).mpr hk)
    rw [Ws49DictInf.KerMin.maximalIdeal_R p, Ideal.mem_span_singleton] at hmem
    exact (Ws49DictInf.KerMin.res_eq_zero_iff p _).mpr hmem
  by_cases hb0 : ((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) = 0
  · rw [hb0]
    exact W₀.mem_nonunits_iff.mpr (by rw [map_zero]; exact zero_lt_one)
  by_contra hnu
  have hle : W₀.valuation ((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) ≤ 1 := (W₀.valuation_le_one_iff _).mpr (hOW b)
  have hv1 : W₀.valuation ((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) = 1 :=
    le_antisymm hle (not_lt.mp (fun h => hnu (W₀.mem_nonunits_iff.mpr h)))
  have hinv : (((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)))⁻¹ ∈ W₀ :=
    (W₀.valuation_le_one_iff _).mp (by rw [map_inv₀, hv1, inv_one])
  obtain ⟨a, a', ha', hEq⟩ := (hW₀ _).mp hinv
  have hsub : (GaloisRep.ratLocalizedAt p).subtype = algebraMap (R p) ℚ := Ws49DictInf.KerMin.ringHom_ext_R p _ _
  rw [hsub] at hEq
  have hbF : ((((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ) ≠ 0 := by
    intro h
    exact hb0 ((ZeroMemClass.coe_eq_zero).mp h)
  have hcoeinv : (((((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)))⁻¹ : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
      (((((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ))⁻¹ :=
    IntermediateField.coe_inv _ _
  have h2 : HahnSeries.ofPowerSeries ℤ ℚ (a'.map (algebraMap (R p) ℚ)) =
      ((((b : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a.map (algebraMap (R p) ℚ)) := by
    rw [← hEq, ← mul_assoc, hcoeinv, mul_inv_cancel₀ hbF, one_mul]
  rw [← hyb, ← coeffMap_ofPowerSeries', ← coeffMap_ofPowerSeries', ← map_mul] at h2
  have h3 : HahnSeries.ofPowerSeries ℤ (R p) a' = y * HahnSeries.ofPowerSeries ℤ (R p) a := coeffMap_rat_injective p h2
  have h4 := congrArg (coeffMap (GaloisRep.ratLocalizedAtResidue p)) h3
  rw [map_mul, hres, zero_mul, coeffMap_ofPowerSeries'] at h4
  exact ha' (HahnSeries.ofPowerSeries_injective (h4.trans (map_zero _).symm))

end Ws49DictInf.Red
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.MultOne"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.MultOne"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hW₀ : (∀ f₀ : ↥(qExpFunctionFieldC ℚ (ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))) :
    ∃ P : Fin 2 → Ideal ↥(chartAlgInf p (ΓM M H) hj),
      (∀ i, P i ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}).minimalPrimes) ∧ P 0 ≠ P 1 ∧
      (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}).minimalPrimes = {P 0, P 1} ∧
      (∀ b : ↥(chartAlgInf p (ΓM M H) hj), b ∈ P 0 ↔ ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) ∈ W₀.nonunits) ∧
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
        [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
        (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
        (i : Fin 2) (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
        (𝔮 : PrimeSpectrum ↥(chartAlgInf p (ΓM M H) hj)),
        (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y =
          (ιInf p (ΓM M H) hj).base 𝔮 →
        (y ∈ Set.range (𝔛.comp A hA ρ hρ i).base ↔ P i ≤ 𝔮.asIdeal) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out

  let F : Type := ↥(qExpFunctionFieldC ℚ (ΓM M H))
  let O : Type := ↥(chartAlgInf p (ΓM M H) hj)

  letI iOcr : CommRing O := (chartAlgInf p (ΓM M H) hj).toCommRing
  letI iOalg : Algebra (R p) O := (chartAlgInf p (ΓM M H) hj).algebra

  obtain ⟨V₀, V₁, g1, g2, g3, g5, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH p M H hpM hpM2 hHp hj
  obtain ⟨W, hWpin, hWR, hWp, hWj, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (ΓM M H) hj
  have hWW₀ : W = W₀ := by
    ext f; exact (hWpin f).trans (hW₀ f).symm
  subst hWW₀
  have key : ∃ W₁ : ValuationSubring F,
      (∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) F a ∈ (![W, W₁] i)) ∧
        ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) F a ∈ (![W, W₁] i).nonunits) ∧
      (∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ (![W, W₁] i) ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ (![W, W₁] i)) ∧
      W ≠ W₁ ∧
      (∀ V : ValuationSubring F,
        (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) F a ∈ V) →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) F a ∈ V.nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (ΓM M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (ΓM M H) hj) Q)⁻¹ ∈ V) →
        V = W ∨ V = W₁) := by
    rcases g5 W hWR hWp hWj with rfl | rfl
    · exact ⟨V₁, g1, g2, g3, g5⟩
    · refine ⟨V₀, ?_, ?_, fun h => g3 h.symm, fun V a b c => (g5 V a b c).symm⟩
      · intro i; fin_cases i
        · exact g1 1
        · exact g1 0
      · intro i; fin_cases i
        · exact g2 1
        · exact g2 0
  obtain ⟨W₁, hW1, hW2, hW3, hW5⟩ := key
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Ws49DictInf.MultOne.finiteIndex_gammaH M H
  have hT := Ws49DictInf.MultOne.T_mem_gammaH M H
  have hFD := Ws49DictInf.KerMin.finiteDimensional_adjoin_jAt (CohCarrier.GammaH M H) hT hj
  have hsep := Ws49DictInf.KerMin.isSeparable_adjoin_jAt (CohCarrier.GammaH M H) hT hj
  obtain ⟨hi, hii, -, -⟩ :=
    Ws49DictInf.KerMin.kerMin_inf_of_pair p M H hj hFD hsep W W₁ hW1 hW2 hW3 hW5
  choose Pf hPf using hii
  have hP0desc : ∀ b : O, b ∈ Pf 0 ↔ ((b : O) : F) ∈ W.nonunits := fun b => (hPf 0).2 b
  have hP1desc : ∀ b : O, b ∈ Pf 1 ↔ ((b : O) : F) ∈ W₁.nonunits := fun b => (hPf 1).2 b

  have hOW : ∀ b : O, ((b : O) : F) ∈ W :=
    (ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
      (CohCarrier.GammaH M H) hT p (jAt (ΓM M H) hj) (coe_jAt _ hj) W hW₀).1
  have hP01 : Pf 0 ≠ Pf 1 := by
    intro heq

    obtain ⟨-, -, ⟨b0, hb0W0, hb0W1⟩, -⟩ :=
      Ws49DictInf.KerMin.kerMin_inf_of_pair p M H hj hFD hsep W W₁ hW1 hW2 hW3 hW5
    have h0 : b0 ∈ Pf 0 := (hP0desc b0).mpr hb0W0
    rw [heq] at h0
    exact hb0W1 ((hP1desc b0).mp h0)
  have hmin : ∀ k, Pf k ∈ (Ideal.span {((p : ℕ) : O)}).minimalPrimes := fun k => (hPf k).1
  have hminset : (Ideal.span {((p : ℕ) : O)}).minimalPrimes = {Pf 0, Pf 1} := by
    ext 𝔭
    constructor
    · intro h𝔭
      rcases hi 𝔭 h𝔭 with h | h
      · left; ext b; rw [h b, hP0desc b]
      · right; ext b; rw [h b, hP1desc b]
    · rintro (rfl | rfl)
      · exact hmin 0
      · exact hmin 1
  refine ⟨Pf, hmin, hP01, hminset, hP0desc, ?_⟩

  intro A hA _ _ ρ hρ i y 𝔮 hy
  letI instAlg : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  let κ : Type := IsLocalRing.ResidueField ↥A
  have halg : algebraMap (R p) κ = (IsLocalRing.residue ↥A).comp ρ := RingHom.algebraMap_toAlgebra _
  let ιR : O →+* κ ⊗[R p] O := (Algebra.TensorProduct.includeRight : O →ₐ[R p] κ ⊗[R p] O).toRingHom

  let c' := Ws49DictInf.Geo.cInf (R p) F (jAt (ΓM M H) hj) κ
  have hc'open : IsOpen (Set.range c'.base) := c'.isOpenEmbedding.isOpen_range

  let ct : ↥(Spec (CommRingCat.of (κ ⊗[R p] O))) → Ideal O := fun z => Ideal.comap ιR z.asIdeal

  have hp0 : ((p : ℕ) : κ ⊗[R p] O) = 0 := by
    rw [← map_natCast (algebraMap κ (κ ⊗[R p] O)) p, CharP.cast_eq_zero κ p, map_zero]
  have hpct : ∀ z, Ideal.span {((p : ℕ) : O)} ≤ ct z := by
    intro z
    rw [Ideal.span_singleton_le_iff_mem]
    show ιR (p : O) ∈ z.asIdeal
    rw [map_natCast, hp0]
    exact Ideal.zero_mem _

  let red := Ws49DictInf.Red.red p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ)
  have hred : ∀ (b : O) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : F) : LaurentSeries ℚ) → red b = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y :=
    fun b y h => Ws49DictInf.Red.red_eq_of_coeffMap_eq p (ΓM M H) hj _ b y h
  have hker : RingHom.ker red = Pf 0 := by
    haveI : (RingHom.ker red).IsPrime := RingHom.ker_isPrime _
    have hle : RingHom.ker red ≤ Pf 0 := fun b hb =>
      (hP0desc b).mpr (Ws49DictInf.Red.coe_mem_nonunits_of_red_eq_zero p (ΓM M H) hj _ W hW₀ hOW b ((RingHom.mem_ker).mp hb))
    have hpker : Ideal.span {((p : ℕ) : O)} ≤ RingHom.ker red := by
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast]
      ext k
      rw [HahnSeries.coeff_zero]
      change ((p : ℕ) : LaurentSeries κ).coeff k = 0
      rw [← map_natCast (algebraMap κ (LaurentSeries κ)) p, CharP.cast_eq_zero κ p, map_zero, HahnSeries.coeff_zero]
    exact le_antisymm hle ((hmin 0).2 ⟨inferInstance, hpker⟩ hle)

  have hD0 : ∀ z : ↥(Spec (CommRingCat.of (κ ⊗[R p] O))),
      c'.base z ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ↔ Pf 0 ≤ ct z := by
    intro z
    rw [ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le 𝔛 A hA ρ hρ halg red hred c'
      (Ws49DictInf.Geo.cInf_fst _ _ _ _) (Ws49DictInf.Geo.cInf_snd _ _ _ _) z, Ideal.map_le_iff_le_comap, hker]
    exact Iff.rfl

  set Z0 : Set ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := Set.range (𝔛.comp A hA ρ hρ 0).base with hZ0
  set Z1 : Set ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := Set.range (𝔛.comp A hA ρ hρ 1).base with hZ1
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  have hZ0closed : IsClosed Z0 := (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isClosed_range
  have hZ1closed : IsClosed Z1 := (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isClosed_range
  have hcover : ∀ x, x ∈ Z0 ∨ x ∈ Z1 := 𝔛.comp_jointly_surjective A hA ρ hρ
  have hnot : ¬ (Z1 ⊆ Z0) := by
    intro hsub

    haveI : IsIso (fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)) := by
      unfold fibreMap overOfIso; infer_instance
    have hwsurj : Function.Surjective (fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)).base :=
      (Scheme.homeoOfIso (asIso (fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)))).surjective
    have hZ0univ : Z0 = Set.univ := Set.eq_univ_of_forall fun x => (hcover x).elim id (fun h => hsub h)
    have hZ1univ : Z1 = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨x', rfl⟩ := hwsurj x
      have hx' : x' ∈ Z0 := by rw [hZ0univ]; exact Set.mem_univ _
      obtain ⟨t, rfl⟩ := hx'
      refine ⟨t, ?_⟩
      rw [← 𝔛.comp_w A hA ρ hρ, Scheme.Hom.comp_apply]
    exact 𝔛.range_comp_ne A hA ρ hρ (hZ0univ.trans hZ1univ.symm)

  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos).ne'⟩
  haveI hint0 : IsIntegral (fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
    ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP (M / p)
      (ΓN p M H hpM) (Ws49DictInf.MultOne.gamma1_le_gammaH (M / p) _) (CohCarrier.GammaH_le_Gamma0 _) p hpN
      (jAt (ΓN p M H hpM) hj) (coe_jAt _ _) κ
  let η := genericPoint ↥(fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
  let ζ1 := (𝔛.comp A hA ρ hρ 1).base η
  have hζ1 : ∀ x ∈ Z1, ζ1 ⤳ x := by
    rintro x ⟨t, rfl⟩
    exact (genericPoint_specializes t).map (𝔛.comp A hA ρ hρ 1).continuous

  have hD1 : ∀ z : ↥(Spec (CommRingCat.of (κ ⊗[R p] O))),
      c'.base z ∈ Z1 ↔ Pf 1 ≤ ct z := by
    intro z
    constructor
    · intro hz

      have hζr : ζ1 ∈ Set.range c'.base := (hζ1 _ hz).mem_open hc'open ⟨z, rfl⟩
      obtain ⟨z1, hz1⟩ := hζr
      have hsp : c'.base z1 ⤳ c'.base z := by rw [hz1]; exact hζ1 _ hz
      have hle : z1.asIdeal ≤ z.asIdeal :=
        (PrimeSpectrum.asIdeal_le_asIdeal z1 z).mpr (Ws49DictInf.Geo.specializes_of_cInf (R p) F (jAt (ΓM M H) hj) κ hsp)
      have hct : ct z1 ≤ ct z := Ideal.comap_mono hle
      obtain ⟨m, hm, hmle⟩ := Ideal.exists_minimalPrimes_le (hpct z1)
      rw [hminset] at hm
      rcases hm with rfl | rfl
      ·
        exfalso
        apply hnot
        intro x hx
        have hζ0 : ζ1 ∈ Z0 := by rw [← hz1]; exact (hD0 z1).mpr hmle
        exact (hζ1 x hx).mem_closed hZ0closed hζ0
      · exact hmle.trans hct
    · intro hP1
      haveI : (Pf 1).IsPrime := (hmin 1).1.1
      have hpP : ((p : ℕ) : O) ∈ Pf 1 := (hmin 1).1.2 (Ideal.subset_span rfl)
      obtain ⟨𝔓', h𝔓'le, h𝔓'prime, h𝔓'P⟩ :=
        GaloisRep.exists_ideal_le_comap_includeRight_eq_of_natCast_mem p κ O (Pf 1) (ct z) hP1 hpP z.asIdeal rfl
      let z' : ↥(Spec (CommRingCat.of (κ ⊗[R p] O))) := ⟨𝔓', h𝔓'prime⟩
      have hz'z : c'.base z' ⤳ c'.base z :=
        ((PrimeSpectrum.le_iff_specializes z' z).mp h𝔓'le).map c'.continuous
      have hz'1 : c'.base z' ∈ Z1 := by
        rcases hcover (c'.base z') with h0 | h1
        · exfalso
          have : Pf 0 ≤ ct z' := (hD0 z').mp h0
          have hP0P1 : Pf 0 ≤ Pf 1 := by rw [← h𝔓'P]; exact this
          exact hP01 (le_antisymm hP0P1 ((hmin 1).2 (hmin 0).1 hP0P1))
        · exact h1
      exact hz'z.mem_closed hZ1closed hz'1

  obtain ⟨𝔓, h𝔓⟩ : y ∈ Set.range c'.base :=
    (Ws49DictInf.Geo.mem_range_cInf_iff (R p) F (jAt (ΓM M H) hj) κ y).mpr ⟨𝔮, hy.symm⟩
  have h𝔮 : 𝔮 = PrimeSpectrum.comap ιR 𝔓 := by
    apply (ιInf p (ΓM M H) hj).isOpenEmbedding.injective
    rw [← hy, ← h𝔓, ← Scheme.Hom.comp_apply, Ws49DictInf.Geo.cInf_fst, Scheme.Hom.comp_apply, Spec.map_apply,
      CommRingCat.hom_ofHom]
  have h𝔮ct : 𝔮.asIdeal = ct 𝔓 := by rw [h𝔮]; rfl
  rw [← h𝔓, h𝔮ct]
  fin_cases i
  · exact hD0 𝔓
  · exact hD1 𝔓

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.Geo P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.KerMin P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le.Ws49DictInf.MultOne"

end S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le (solution)
