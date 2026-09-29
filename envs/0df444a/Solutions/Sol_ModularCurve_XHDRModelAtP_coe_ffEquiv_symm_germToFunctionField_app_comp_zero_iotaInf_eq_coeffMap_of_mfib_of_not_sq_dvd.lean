-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4b35c253-ba7f-57e0-a3f1-095d37474dba

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_XH
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_nonunits_gauss_of_ffEquiv_symm_germToFunctionField_app_comp_zero_eq_zero
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace LaurentSeries p2m_export "LaurentSeries" "powerSeriesPart ofPowerSeries_powerSeriesPart single_order_mul_powerSeriesPart" end LaurentSeries
p2m_open_scoped "LaurentSeries" in

theorem LaurentSeries.eq_zero_of_sum_smul_eq_zero_of_linearIndependent
    {κ : Type*} [Field κ] (k₀ : Subfield κ) {ι : Type*} [Fintype ι]
    (e : ι → κ) (he : LinearIndependent k₀ e)
    (g : ι → LaurentSeries κ) (hg : ∀ i (n : ℤ), (g i).coeff n ∈ k₀)
    (h : ∑ i, e i • g i = 0) : ∀ i, g i = 0 := by
  classical
  intro i
  ext n
  rw [HahnSeries.coeff_zero]

  have hn : ∑ j, e j * (g j).coeff n = 0 := by
    have h1 := congrArg (fun x : LaurentSeries κ => x.coeff n) h
    simpa [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul] using h1

  have hrel : ∑ j, (⟨(g j).coeff n, hg j n⟩ : k₀) • e j = 0 := by
    rw [← hn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  have h0 := Fintype.linearIndependent_iff.mp he (fun j => ⟨(g j).coeff n, hg j n⟩) hrel i
  exact congrArg Subtype.val h0

namespace GaloisRep p2m_export "GaloisRep" "ratLocalizedAt ratLocalizedAtResidue isLocalization_ratLocalizedAt isFractionRing_ratLocalizedAt ratLocalizedAt.isLocalRing ratLocalizedAt.maximalIdeal_eq_span_natCast" end GaloisRep
p2m_open_scoped "GaloisRep" in

theorem GaloisRep.residue_ratLocalizedAt_mem_bot
    (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A] [IsLocalRing A] [CharP (IsLocalRing.ResidueField A) p]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* A) (r : ↥(GaloisRep.ratLocalizedAt p)) :
    IsLocalRing.residue A (ρ r) ∈ (⊥ : Subfield (IsLocalRing.ResidueField A)) := by
  classical
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Ideal.span {(p : ℤ)}).primeCompl r

  have hb : ¬ (p : ℤ) ∣ (b : ℤ) := fun hd => b.2 (Ideal.mem_span_singleton.mpr hd)
  have hbκ : ((b : ℤ) : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Ne, CharP.intCast_eq_zero_iff (IsLocalRing.ResidueField A) p]
    exact hb
  have h1 : IsLocalRing.residue A (ρ r) * ((b : ℤ) : IsLocalRing.ResidueField A) = ((a : ℤ) : IsLocalRing.ResidueField A) := by
    have h2 := congrArg (fun x => IsLocalRing.residue A (ρ x)) hab
    simp only [map_mul, map_intCast, eq_intCast] at h2
    exact h2
  rw [show IsLocalRing.residue A (ρ r) = ((a : ℤ) : IsLocalRing.ResidueField A) / ((b : ℤ) : IsLocalRing.ResidueField A) by
    rw [eq_div_iff hbκ]; exact h1]
  exact div_mem (intCast_mem _ a) (intCast_mem _ b)

namespace LaurentSeries
p2m_export "LaurentSeries" "powerSeriesPart ofPowerSeries_powerSeriesPart single_order_mul_powerSeriesPart"
namespace PFDescent
p2m_open "LaurentSeries"

theorem linDisj
    {κ : Type*} [Field κ] (k₀ : Subfield κ) {ι : Type*} [Fintype ι]
    (e : ι → κ) (he : LinearIndependent k₀ e)
    (g : ι → LaurentSeries κ) (hg : ∀ i (n : ℤ), (g i).coeff n ∈ k₀)
    (h : ∑ i, e i • g i = 0) : ∀ i, g i = 0 := by
  classical
  intro i
  ext n
  rw [HahnSeries.coeff_zero]
  have hn : ∑ j, e j * (g j).coeff n = 0 := by
    have h1 := congrArg (fun x : LaurentSeries κ => x.coeff n) h
    simpa [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul] using h1
  have hrel : ∑ j, (⟨(g j).coeff n, hg j n⟩ : k₀) • e j = 0 := by
    rw [← hn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  have h0 := Fintype.linearIndependent_iff.mp he (fun j => ⟨(g j).coeff n, hg j n⟩) hrel i
  exact congrArg Subtype.val h0

theorem exists_natCast_eq_of_mem_bot {κ : Type*} [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (μ : κ) (hμ : μ ∈ (⊥ : Subfield κ)) : ∃ n : ℕ, (n : κ) = μ := by
  have hle : (⊥ : Subfield κ) ≤ (ZMod.castHom (dvd_refl p) κ).fieldRange := bot_le
  obtain ⟨z, hz⟩ := hle hμ
  refine ⟨z.val, ?_⟩
  rw [← hz, ZMod.castHom_apply, ZMod.natCast_val]

theorem coeff_mul_mem {κ : Type*} [Field κ] (k₀ : Subfield κ) (y z : LaurentSeries κ)
    (hy : ∀ n : ℤ, y.coeff n ∈ k₀) (hz : ∀ n : ℤ, z.coeff n ∈ k₀) (n : ℤ) : (y * z).coeff n ∈ k₀ := by
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hy _) (hz _)

theorem coeff_sub_mem {κ : Type*} [Field κ] (k₀ : Subfield κ) (y z : LaurentSeries κ)
    (hy : ∀ n : ℤ, y.coeff n ∈ k₀) (hz : ∀ n : ℤ, z.coeff n ∈ k₀) (n : ℤ) : (y - z).coeff n ∈ k₀ := by
  rw [HahnSeries.coeff_sub]
  exact sub_mem (hy n) (hz n)

end LaurentSeries.PFDescent

p2m_open_scoped "LaurentSeries" in
open MvPolynomial in

theorem LaurentSeries.exists_mul_eq_of_mem_adjoin_range_of_coeff_mem_bot
    {κ : Type*} [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    {B : Type*} [CommRing B] (r : B →+* LaurentSeries κ)
    (hr : ∀ b (n : ℤ), (r b).coeff n ∈ (⊥ : Subfield κ))
    (x : LaurentSeries κ) (hx : x ∈ IntermediateField.adjoin κ (Set.range r))
    (hxc : ∀ n : ℤ, x.coeff n ∈ (⊥ : Subfield κ)) :
    ∃ s t : B, r t ≠ 0 ∧ x * r t = r s := by
  classical
  set k₀ : Subfield κ := ⊥ with hk₀

  have halg : ∀ c : κ, algebraMap κ (LaurentSeries κ) c = HahnSeries.single 0 c := by
    intro c
    have h1 : algebraMap κ (PowerSeries κ) c = PowerSeries.C c := by simp
    rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
    rfl
  have hsm : ∀ (a : κ) (y : LaurentSeries κ), a • y = algebraMap κ (LaurentSeries κ) a * y := by
    intro a y
    rw [halg]
    ext n
    rw [HahnSeries.coeff_smul, HahnSeries.coeff_single_zero_mul, smul_eq_mul]

  obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_iff κ x).mp hx

  have hpre0 : ∀ v : Set.range r, ∃ b : B, r b = v := fun v => v.2
  choose pre hpre using hpre0
  let β : ((Set.range r) →₀ ℕ) → B := fun m => m.prod fun v k => pre v ^ k
  have hmon : ∀ m : (Set.range r) →₀ ℕ, (m.prod fun v k => (v : LaurentSeries κ) ^ k) = r (β m) := by
    intro m
    simp only [β, Finsupp.prod, map_prod, map_pow, hpre]

  let Cf : Finset κ := P.support.image (fun m => P.coeff m) ∪ Q.support.image (fun m => Q.coeff m)
  let W : Submodule k₀ κ := Submodule.span k₀ (Cf : Set κ)
  haveI : FiniteDimensional k₀ W := FiniteDimensional.span_of_finite k₀ Cf.finite_toSet
  let bW := Module.finBasis k₀ W
  let e : Fin (Module.finrank k₀ W) → κ := fun i => (bW i : κ)
  have he : LinearIndependent k₀ e := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hdec : ∀ (c : κ) (hc : c ∈ W), c = ∑ i, ((bW.repr ⟨c, hc⟩ i : k₀) : κ) * e i := by
    intro c hc
    have h1 := bW.sum_repr ⟨c, hc⟩
    have h2 := congrArg (fun w : W => (w : κ)) h1
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] at h2
    refine h2.symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subfield.smul_def, smul_eq_mul]
  have hPW : ∀ m, m ∈ P.support → P.coeff m ∈ W := fun m hm =>
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)))
  have hQW : ∀ m, m ∈ Q.support → Q.coeff m ∈ W := fun m hm =>
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)))

  have hnat := LaurentSeries.PFDescent.exists_natCast_eq_of_mem_bot (κ := κ) p
  choose natOf hnatOf using hnat
  let cP : ((Set.range r) →₀ ℕ) → Fin (Module.finrank k₀ W) → ℕ := fun m i =>
    if hm : m ∈ P.support then natOf _ (bW.repr ⟨P.coeff m, hPW m hm⟩ i).2 else 0
  let cQ : ((Set.range r) →₀ ℕ) → Fin (Module.finrank k₀ W) → ℕ := fun m i =>
    if hm : m ∈ Q.support then natOf _ (bW.repr ⟨Q.coeff m, hQW m hm⟩ i).2 else 0
  have hcP : ∀ m (hm : m ∈ P.support) i, ((cP m i : ℕ) : κ) = ((bW.repr ⟨P.coeff m, hPW m hm⟩ i : k₀) : κ) := by
    intro m hm i
    simp only [cP, dif_pos hm, hnatOf]
  have hcQ : ∀ m (hm : m ∈ Q.support) i, ((cQ m i : ℕ) : κ) = ((bW.repr ⟨Q.coeff m, hQW m hm⟩ i : k₀) : κ) := by
    intro m hm i
    simp only [cQ, dif_pos hm, hnatOf]

  let σ : Fin (Module.finrank k₀ W) → B := fun i => ∑ m ∈ P.support, (cP m i : B) * β m
  let τ : Fin (Module.finrank k₀ W) → B := fun i => ∑ m ∈ Q.support, (cQ m i : B) * β m
  have hexp : ∀ (R : MvPolynomial (Set.range r) κ) (c : ((Set.range r) →₀ ℕ) → Fin (Module.finrank k₀ W) → ℕ)
      (hRW : ∀ m, m ∈ R.support → R.coeff m ∈ W)
      (hc : ∀ m (hm : m ∈ R.support) i, ((c m i : ℕ) : κ) = ((bW.repr ⟨R.coeff m, hRW m hm⟩ i : k₀) : κ)),
      aeval Subtype.val R = ∑ i, e i • r (∑ m ∈ R.support, (c m i : B) * β m) := by
    intro R c hRW hc
    conv_lhs => rw [R.as_sum]
    rw [map_sum]
    have h1 : ∀ m ∈ R.support, aeval (Subtype.val : Set.range r → LaurentSeries κ) (monomial m (R.coeff m)) =
        ∑ i, e i • (((c m i : ℕ) : LaurentSeries κ) * r (β m)) := by
      intro m hm
      rw [aeval_monomial, hmon, hdec (R.coeff m) (hRW m hm), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc m hm i, map_mul, map_natCast, hsm]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.smul_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_natCast]
  have hN := hexp P cP hPW hcP
  have hD := hexp Q cQ hQW hcQ

  have hrsum : ∀ (f : Fin (Module.finrank k₀ W) → B), True := fun _ => trivial
  by_cases hD0 : aeval (Subtype.val : Set.range r → LaurentSeries κ) Q = 0
  ·
    refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [hPQ, hD0, div_zero, map_one, map_zero, zero_mul]
  · have hxD : x * aeval (Subtype.val : Set.range r → LaurentSeries κ) Q = aeval Subtype.val P := by
      rw [hPQ, div_mul_cancel₀ _ hD0]

    have hrel : ∑ i, e i • (x * r (τ i) - r (σ i)) = 0 := by
      have h1 : ∑ i, e i • (x * r (τ i) - r (σ i)) = x * (∑ i, e i • r (τ i)) - ∑ i, e i • r (σ i) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsm, hsm, hsm]
        ring
      rw [h1]
      change x * (∑ i, e i • r (∑ m ∈ Q.support, (cQ m i : B) * β m)) - ∑ i, e i • r (∑ m ∈ P.support, (cP m i : B) * β m) = 0
      rw [← hD, ← hN, hxD, sub_self]
    have hg : ∀ i (n : ℤ), (x * r (τ i) - r (σ i)).coeff n ∈ k₀ := fun i n =>
      LaurentSeries.PFDescent.coeff_sub_mem k₀ _ _
        (LaurentSeries.PFDescent.coeff_mul_mem k₀ _ _ hxc (hr _)) (hr _) n
    have hzero := LaurentSeries.PFDescent.linDisj k₀ e he _ hg hrel

    have hex : ∃ i, r (τ i) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hD0
      rw [hD]
      refine Finset.sum_eq_zero fun i _ => ?_
      change e i • r (τ i) = 0
      rw [hall i, smul_zero]
    obtain ⟨i, hi⟩ := hex
    exact ⟨σ i, τ i, hi, sub_eq_zero.mp (hzero i)⟩

namespace ReadChartInfM

theorem coeffMap_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simpa [coeffMap_coeff] using this

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem exists_unique_lift (b : ↥(chartAlgInf p Γ hj)) :
    ∃! y : LaurentSeries (R p), coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := by
  obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    Γ p (jAt Γ hj) (coe_jAt Γ hj)).2 b
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  refine ⟨y, hy, fun y' hy' => coeffMap_injective _ (IsFractionRing.injective (R p) ℚ) (hy'.trans hy.symm)⟩

noncomputable def lift (b : ↥(chartAlgInf p Γ hj)) : LaurentSeries (R p) :=
  Classical.choose (exists_unique_lift p Γ hj b).exists

theorem lift_spec (b : ↥(chartAlgInf p Γ hj)) :
    coeffMap (algebraMap (R p) ℚ) (lift p Γ hj b) = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) :=
  Classical.choose_spec (exists_unique_lift p Γ hj b).exists

theorem lift_eq_of_coeffMap_eq (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) :
    lift p Γ hj b = y :=
  (exists_unique_lift p Γ hj b).unique (lift_spec p Γ hj b) hy

theorem lift_mul (b c : ↥(chartAlgInf p Γ hj)) : lift p Γ hj (b * c) = lift p Γ hj b * lift p Γ hj c := by
  apply lift_eq_of_coeffMap_eq
  rw [map_mul, lift_spec, lift_spec]
  push_cast
  rfl

theorem lift_add (b c : ↥(chartAlgInf p Γ hj)) : lift p Γ hj (b + c) = lift p Γ hj b + lift p Γ hj c := by
  apply lift_eq_of_coeffMap_eq
  rw [map_add, lift_spec, lift_spec]
  push_cast
  rfl

theorem lift_one : lift p Γ hj 1 = 1 := by
  apply lift_eq_of_coeffMap_eq
  rw [map_one]; push_cast; rfl

theorem lift_zero : lift p Γ hj 0 = 0 := by
  apply lift_eq_of_coeffMap_eq
  rw [map_zero]; push_cast; rfl

noncomputable def red {κ : Type*} [CommRing κ] (τ : R p →+* κ) : ↥(chartAlgInf p Γ hj) →+* LaurentSeries κ where
  toFun b := coeffMap τ (lift p Γ hj b)
  map_one' := by rw [lift_one, map_one]
  map_mul' b c := by rw [lift_mul, map_mul]
  map_zero' := by rw [lift_zero, map_zero]
  map_add' b c := by rw [lift_add, map_add]

theorem red_eq_of_coeffMap_eq {κ : Type*} [CommRing κ] (τ : R p →+* κ) (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) :
    red p Γ hj τ b = coeffMap τ y := by
  show coeffMap τ (lift p Γ hj b) = _
  rw [lift_eq_of_coeffMap_eq p Γ hj b y hy]

theorem red_coeff_mem_range {κ : Type*} [CommRing κ] (τ : R p →+* κ) (b : ↥(chartAlgInf p Γ hj)) (n : ℤ) :
    (red p Γ hj τ b).coeff n ∈ Set.range τ :=
  ⟨_, rfl⟩

theorem coeffMap_ofPowerSeries {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A x) = HahnSeries.ofPowerSeries ℤ B (x.map f) := by
  ext n
  rw [coeffMap_coeff]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · have hA : (HahnSeries.ofPowerSeries ℤ A x).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      simp only [Set.mem_range, not_exists]
      intro m hm
      apply hn
      rw [← hm]
      exact Int.natCast_nonneg m
    have hB : (HahnSeries.ofPowerSeries ℤ B (x.map f)).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      simp only [Set.mem_range, not_exists]
      intro m hm
      apply hn
      rw [← hm]
      exact Int.natCast_nonneg m
    rw [hA, hB, map_zero]

theorem exists_gauss_presentation (y : LaurentSeries (R p)) :
    ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      coeffMap (algebraMap (R p) ℚ) y * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype) := by
  have hsub : (GaloisRep.ratLocalizedAt p).subtype = algebraMap (R p) ℚ := rfl
  rw [hsub]
  by_cases hord : y.order ≤ 0
  · refine ⟨y.powerSeriesPart, PowerSeries.X ^ (-y.order).toNat, ?_, ?_⟩
    · rw [map_pow, PowerSeries.map_X]
      exact pow_ne_zero _ PowerSeries.X_ne_zero
    · rw [← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries, ← map_mul, HahnSeries.ofPowerSeries_X_pow,
        LaurentSeries.ofPowerSeries_powerSeriesPart, mul_comm]
      congr 2
      rw [Int.toNat_of_nonneg (by omega)]
  · push_neg at hord
    refine ⟨PowerSeries.X ^ y.order.toNat * y.powerSeriesPart, 1, ?_, ?_⟩
    · rw [map_one]; exact one_ne_zero
    · rw [map_one, ← coeffMap_ofPowerSeries, map_mul, HahnSeries.ofPowerSeries_X_pow,
        Int.toNat_of_nonneg hord.le, LaurentSeries.single_order_mul_powerSeriesPart]
      simp

section kernel

variable {κ : Type*} [Field κ] (τ : R p →+* κ) (hτp : τ ((p : ℕ) : R p) = 0)
  (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
  (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
    ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
  (hW₀R : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r ∈ W₀)
  (hW₀p : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ W₀.nonunits)
  (hW₀6 : ∀ x : ↥(qExpFunctionFieldC ℚ Γ), x ∈ W₀.nonunits →
    x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀)

include hW₀ hW₀R hW₀p hW₀6 hτp

theorem red_eq_zero_iff_mem_nonunits (b : ↥(chartAlgInf p Γ hj)) :
    red p Γ hj τ b = 0 ↔ (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀.nonunits := by
  haveI : IsLocalRing (R p) := GaloisRep.ratLocalizedAt.isLocalRing (Fact.out : p.Prime)
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hmaxR : IsLocalRing.maximalIdeal (R p) = Ideal.span {((p : ℕ) : R p)} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p (Fact.out)

  have hkerτ : ∀ r : R p, τ r = 0 ↔ r ∈ Ideal.span {((p : ℕ) : R p)} := by
    intro r
    constructor
    · intro hr
      rw [← hmaxR]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top τ) ((RingHom.mem_ker).mpr hr)
    · intro hr
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      rw [map_mul, hτp, mul_zero]

  have hcoe : ∀ b' : ↥(chartAlgInf p Γ hj), ((b' : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
      coeffMap (algebraMap (R p) ℚ) (lift p Γ hj b') := fun b' => (lift_spec p Γ hj b').symm
  have hsub : (GaloisRep.ratLocalizedAt p).subtype = algebraMap (R p) ℚ := rfl
  have hinjQ : Function.Injective (coeffMap (algebraMap (R p) ℚ)) :=
    coeffMap_injective _ (IsFractionRing.injective (R p) ℚ)

  have halgp : ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : R p) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = HahnSeries.C (p : ℚ) := by
    rw [map_natCast]
    push_cast
    rw [← map_natCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ)]
  have hCp : coeffMap (algebraMap (R p) ℚ) (HahnSeries.C ((p : ℕ) : R p)) = HahnSeries.C (p : ℚ) := by
    show (HahnSeries.C _).map _ = _
    rw [HahnSeries.map_C, map_natCast]
  constructor
  ·
    intro hred
    have hcoef : ∀ n : ℤ, (lift p Γ hj b).coeff n ∈ Ideal.span {((p : ℕ) : R p)} := fun n => by
      rw [← hkerτ]
      have := congrArg (fun z => HahnSeries.coeff z n) hred
      simpa [red, coeffMap_coeff] using this
    choose c hc using fun n => Ideal.mem_span_singleton'.mp (hcoef n)
    let y₁ : LaurentSeries (R p) :=
      { coeff := fun n => if (lift p Γ hj b).coeff n = 0 then 0 else c n
        isPWO_support' := (lift p Γ hj b).isPWO_support.mono (by
          intro n hn
          simp only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall, exists_prop] at hn
          exact hn.1) }
    have hy₁ : lift p Γ hj b = HahnSeries.C ((p : ℕ) : R p) * y₁ := by
      apply HahnSeries.ext; funext n
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
      show _ = _ * (if (lift p Γ hj b).coeff n = 0 then 0 else c n)
      split_ifs with h
      · rw [h, mul_zero]
      · rw [mul_comm, hc n]
    set f : ↥(qExpFunctionFieldC ℚ Γ) := (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : R p))⁻¹ * (b : ↥(qExpFunctionFieldC ℚ Γ)) with hf
    have hp0 : (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : R p)) ≠ 0 := by
      rw [map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hCp0 : (HahnSeries.C (p : ℚ) : LaurentSeries ℚ) ≠ 0 :=
      HahnSeries.C_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hfexp : ((f : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = coeffMap (algebraMap (R p) ℚ) y₁ := by
      rw [hf]
      push_cast
      rw [← map_natCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) p, hcoe, hy₁, map_mul, hCp, ← mul_assoc,
        inv_mul_cancel₀ hCp0, one_mul]
    obtain ⟨a, a', ha', heq⟩ := exists_gauss_presentation p y₁
    have hfW : f ∈ W₀ := (hW₀ f).mpr ⟨a, a', ha', by rw [hfexp]; exact heq⟩
    have hbf : (b : ↥(qExpFunctionFieldC ℚ Γ)) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : R p) * f := by
      rw [hf, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
    rw [hbf]
    have h1 : (⟨_, hW₀R ((p : ℕ) : R p)⟩ : W₀) * ⟨f, hfW⟩ ∈ IsLocalRing.maximalIdeal ↥W₀ :=
      Ideal.mul_mem_right _ _ ((ValuationSubring.coe_mem_nonunits_iff).mp hW₀p)
    exact (ValuationSubring.coe_mem_nonunits_iff).mpr h1
  ·
    intro hb
    obtain ⟨a, a', ha', heq⟩ := (hW₀ _).mp (hW₀6 _ hb)
    have hp0 : (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) ((p : ℕ) : R p)) ≠ 0 := by
      rw [map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero

    have heqR : lift p Γ hj b * HahnSeries.ofPowerSeries ℤ _ a' = HahnSeries.C ((p : ℕ) : R p) * HahnSeries.ofPowerSeries ℤ _ a := by
      apply hinjQ
      rw [map_mul, map_mul, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, hCp, ← hcoe, ← hsub, ← heq]
      push_cast
      rw [← map_natCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) p]
      have hCp0 : (HahnSeries.C (p : ℚ) : LaurentSeries ℚ) ≠ 0 :=
        HahnSeries.C_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      conv_rhs => rw [mul_comm (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) (HahnSeries.C (p : ℚ))⁻¹, mul_assoc (HahnSeries.C (p : ℚ))⁻¹,
        ← mul_assoc (HahnSeries.C (p : ℚ)), mul_inv_cancel₀ hCp0, one_mul]

    have hredeq := congrArg (coeffMap τ) heqR
    rw [map_mul, map_mul, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries] at hredeq
    have hC0 : coeffMap τ (HahnSeries.C ((p : ℕ) : R p)) = 0 := by
      show (HahnSeries.C _).map τ = 0
      rw [HahnSeries.map_C, hτp, HahnSeries.C_zero]
    rw [hC0, zero_mul] at hredeq

    have ha'τ : HahnSeries.ofPowerSeries ℤ κ (a'.map τ) ≠ 0 := by
      intro h0
      apply ha'
      have h0' : a'.map τ = 0 := HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
      ext n
      rw [PowerSeries.coeff_map, map_zero]
      have hn : τ (PowerSeries.coeff n a') = 0 := by
        have := congrArg (PowerSeries.coeff n) h0'
        rwa [PowerSeries.coeff_map, map_zero] at this
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hkerτ _).mp hn)
      rw [← hc, map_mul, map_natCast, ZMod.natCast_self, mul_zero]
    exact (mul_eq_zero.mp hredeq).resolve_right ha'τ

end kernel

section membership

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

include hA hρ hpM2 hHp

theorem red_mem_qExpFunctionFieldC (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (x : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A))
    (b : ↥(chartAlgInf p Γ hj)) :
    red p Γ hj ((IsLocalRing.residue ↥A).comp ρ) b ∈ qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ := by
  obtain ⟨V, hRV, ρV, -, -, -, -, -, hadj, hpin, hpres⟩ :=
    ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
      Γ hT p (jAt Γ hj) (coe_jAt Γ hj) A hA ρ hρ x hx

  have hpresb : coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) * coeffMap A.subtype 1 =
      coeffMap A.subtype (coeffMap ρ (lift p Γ hj b)) := by
    rw [map_one, mul_one, ← lift_spec p Γ hj b, coeffMap_coeffMap, hρ, coeffEmb, coeffMap_coeffMap]
    congr 1
  have h10 : coeffMap (IsLocalRing.residue ↥A) (1 : LaurentSeries ↥A) ≠ 0 := by
    rw [map_one]; exact one_ne_zero
  have hbV : (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ V := (hpin _).mpr ⟨1, _, h10, hpresb⟩
  have hval : ρV ⟨_, hbV⟩ = red p Γ hj ((IsLocalRing.residue ↥A).comp ρ) b := by
    have := hpres ⟨_, hbV⟩ 1 _ h10 hpresb
    rw [map_one, mul_one, coeffMap_coeffMap] at this
    rw [this]
    exact (red_eq_of_coeffMap_eq p Γ hj _ b _ (lift_spec p Γ hj b)).symm
  rw [← hval, ← hadj]
  exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩

theorem qExpFunctionFieldC_infSubgroup_le_adjoin_range_red
    [NeZero (M / p)]
    (x : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A)) :
    qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤
      IntermediateField.adjoin (IsLocalRing.ResidueField ↥A) (Set.range (red p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex := CuspForm.GammaH_finiteIndex (M / p) _
  have hT : ModularGroup.T ∈ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) := ModularCurve.translation_mem_GammaH _ _
  haveI : IsLocalRing (R p) := GaloisRep.ratLocalizedAt.isLocalRing (Fact.out : p.Prime)
  have hmaxR : IsLocalRing.maximalIdeal (R p) = Ideal.span {((p : ℕ) : R p)} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p (Fact.out)

  have hτp : ((IsLocalRing.residue ↥A).comp ρ) ((p : ℕ) : R p) = 0 := by
    rw [RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa [ValuationSubring.LiesOverPrime] using hA

  obtain ⟨V, hRV, ρV, hpV, hQV, -, -, -, hadj, hpin, hpres⟩ :=
    ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
      (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT p (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) (coe_jAt _ hj) A hA ρ hρ x hx

  obtain ⟨W₀, hW₀, hW₀R, hW₀p, hW₀j, hW₀6⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj
  have hratp : GaloisRep.ratLocalizedAtResidue p ((p : ℕ) : R p) = 0 := by
    rw [map_natCast, ZMod.natCast_self]
  have hVW : V = W₀ := by
    refine ModularCurve.XHDRLevel.valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd p M H hpM hpM2 hHp hj V W₀
      hRV ?_ ?_ hW₀R hW₀p hW₀j
    · intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      have h1 : (⟨_, hRV c⟩ : V) * ⟨_, (hRV ((p : ℕ) : R p))⟩ ∈ IsLocalRing.maximalIdeal ↥V :=
        Ideal.mul_mem_left _ _ ((ValuationSubring.coe_mem_nonunits_iff).mp hpV)
      exact (ValuationSubring.coe_mem_nonunits_iff).mpr h1
    · intro Q hQ
      apply hQV
      rintro ⟨Q₁, rfl⟩
      apply hQ
      rw [Polynomial.map_mul, Polynomial.map_C, hratp, map_zero, zero_mul]
  subst hVW

  obtain ⟨hBW, 𝔮, h𝔮, -, -, -, -, -, -⟩ :=
    ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
      (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT p (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) (coe_jAt _ hj) V hW₀

  have hval : ∀ b : ↥(chartAlgInf p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj), ρV ⟨_, hBW b⟩ = red p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ) b := by
    intro b
    have hpresb : coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) : LaurentSeries ℚ) * coeffMap A.subtype 1 =
        coeffMap A.subtype (coeffMap ρ (lift p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj b)) := by
      rw [map_one, mul_one, ← lift_spec p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj b, coeffMap_coeffMap, hρ, coeffEmb, coeffMap_coeffMap]
      congr 1
    have h10 : coeffMap (IsLocalRing.residue ↥A) (1 : LaurentSeries ↥A) ≠ 0 := by
      rw [map_one]; exact one_ne_zero
    have := hpres ⟨_, hBW b⟩ 1 _ h10 hpresb
    rw [map_one, mul_one, coeffMap_coeffMap] at this
    rw [this]
    exact (red_eq_of_coeffMap_eq p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj _ b _ (lift_spec p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj b)).symm

  have hred0 : ∀ t : ↥(chartAlgInf p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj), t ∉ 𝔮 → red p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ) t ≠ 0 := by
    intro t ht h0
    exact ht ((h𝔮 t).mpr ((red_eq_zero_iff_mem_nonunits p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ) hτp V hW₀ hW₀R
      (hW₀p _ (Ideal.mem_span_singleton_self _)) hW₀6 t).mp h0))

  rw [← hadj]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨v, rfl⟩
  obtain ⟨a, t, ht, hvt⟩ := (ModularCurve.mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
    (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT p (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) (coe_jAt _ hj) V hW₀ 𝔮 h𝔮 (v : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))).mp v.2
  have hmul : ρV v * ρV ⟨_, hBW t⟩ = ρV ⟨_, hBW a⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hvt
  rw [hval, hval] at hmul
  have hv : ρV v = red p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ) a * (red p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ) t)⁻¹ := by
    rw [← hmul, mul_inv_cancel_right₀ (hred0 t ht)]
  rw [hv]
  exact mul_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
    (inv_mem (IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩))

theorem red_mem_adjoin_range_red
    [NeZero (M / p)]
    (x : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A))
    (b : ↥(chartAlgInf p (CohCarrier.GammaH M H) hj)) :
    red p (CohCarrier.GammaH M H) hj ((IsLocalRing.residue ↥A).comp ρ) b ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField ↥A) (Set.range (red p (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  have hle := ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  have hxM : (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) ∈ qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H) :=
    qExpFunctionFieldC_mono (IsLocalRing.ResidueField ↥A) hle x.2

  have h1 := red_mem_qExpFunctionFieldC p hj M H hpM hpM2 hHp A hA ρ hρ (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH _ _)
    ⟨_, hxM⟩ hx b

  have h2 := ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp (IsLocalRing.ResidueField ↥A) h1

  exact qExpFunctionFieldC_infSubgroup_le_adjoin_range_red p hj M H hpM hpM2 hHp A hA ρ hρ x hx h2

end membership

end ReadChartInfM

namespace ReadChartInf

universe u

theorem appLE_appIso_inv_eq {S₁ S₂ X₁ X₂ : Scheme.{u}} (ι₁ : S₁ ⟶ X₁) (ι₂ : S₂ ⟶ X₂) [IsOpenImmersion ι₁] [IsOpenImmersion ι₂]
    (π : X₁ ⟶ X₂) (σ : S₁ ⟶ S₂) (hsq : ι₁ ≫ π = σ ≫ ι₂)
    (hV : ι₁ ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι₂ ''ᵁ ⊤)) (s : Γ(S₂, ⊤)) :
    (π.appLE (ι₂ ''ᵁ ⊤) (ι₁ ''ᵁ ⊤) hV).hom ((ι₂.appIso ⊤).inv.hom s) = (ι₁.appIso ⊤).inv.hom (σ.appTop.hom s) := by
  apply (ι₁.appIso ⊤).commRingCatIsoToRingEquiv.injective
  change ((π.appLE (ι₂ ''ᵁ ⊤) (ι₁ ''ᵁ ⊤) hV) ≫ (ι₁.appIso ⊤).hom).hom _ = ((ι₁.appIso ⊤).inv ≫ (ι₁.appIso ⊤).hom).hom _
  rw [Iso.inv_hom_id, Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  have hgen : ∀ (φ : S₁ ⟶ X₂) (hφ : φ = σ ≫ ι₂) (e : (⊤ : S₁.Opens) ≤ φ ⁻¹ᵁ (ι₂ ''ᵁ ⊤)),
      (φ.appLE (ι₂ ''ᵁ ⊤) ⊤ e).hom ((ι₂.appIso ⊤).inv.hom s) = σ.appTop.hom s := by
    rintro φ rfl e
    rw [← Scheme.Hom.appLE_comp_appLE σ ι₂ (ι₂ ''ᵁ ⊤) ⊤ ⊤ (Scheme.Hom.preimage_image_eq _ _).ge le_top]
    rw [CommRingCat.comp_apply, ← Scheme.Hom.appIso_hom']
    rw [← CommRingCat.comp_apply (ι₂.appIso ⊤).inv, Iso.inv_hom_id, CommRingCat.id_apply]
    rw [show ∀ e', σ.appLE ⊤ ⊤ e' = σ.appTop from fun _ => Scheme.Hom.appLE_eq_app _]
  rw [CommRingCat.id_apply]
  exact hgen _ hsq _

theorem germToFunctionField_app_eq_of_appLE_eq {M X₁ X₂ : Scheme.{u}} [IrreducibleSpace M]
    (g : M ⟶ X₁) (π : X₁ ⟶ X₂) (f' : M ⟶ X₂) (hf' : f' = g ≫ π)
    (V₁ : X₁.Opens) (V₂ : X₂.Opens) (hV : V₁ ≤ π ⁻¹ᵁ V₂)
    (s₁ : Γ(X₁, V₁)) (s₂ : Γ(X₂, V₂)) (hs : (π.appLE V₂ V₁ hV).hom s₂ = s₁)
    [h₁ : Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V₁))] [h₂ : Nonempty (Scheme.Opens.toScheme (f' ⁻¹ᵁ V₂))] :
    M.germToFunctionField (g ⁻¹ᵁ V₁) ((g.app V₁).hom s₁) = M.germToFunctionField (f' ⁻¹ᵁ V₂) ((f'.app V₂).hom s₂) := by
  subst hf'
  have hUle : g ⁻¹ᵁ V₁ ≤ (g ≫ π) ⁻¹ᵁ V₂ := fun x hx => hV hx
  have h1 : ((g ≫ π).appLE V₂ (g ⁻¹ᵁ V₁) hUle).hom s₂ = (g.app V₁).hom s₁ := by
    rw [← Scheme.Hom.appLE_comp_appLE g π V₂ V₁ (g ⁻¹ᵁ V₁) hV le_rfl, CommRingCat.comp_apply, hs,
      Scheme.Hom.appLE_eq_app]
  rw [← h1, Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hUle) _ _ _

end ReadChartInf

namespace ReadChartInfM

set_option maxHeartbeats 3200000 in

theorem efib_fst_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    (𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) = (𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ≫ 𝔓.π.1 := by
  simp only [Category.assoc]
  congr 1
  have hmap : XHDRLevel.fibreMap 𝔓.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ≫ 𝔓.π.1 := by
    delta XHDRLevel.fibreMap
    erw [pullback.lift_fst]
  rw [← hmap, ← Category.assoc, 𝔓.comp_pi A hA ρ hρ, Category.id_comp]

set_option maxHeartbeats 3200000 in

theorem nonempty_preimage
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))) := by
  obtain ⟨z, hz⟩ := 𝔓.εinf_mem_comp0 A hA ρ hρ ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A), rfl⟩
  haveI := 𝔓.efib_iso A hA ρ hρ
  refine ⟨⟨(inv (𝔓.efib A hA ρ hρ)).base z, ?_⟩⟩
  show ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).base ((inv (𝔓.efib A hA ρ hρ)).base z) ∈ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)
  have h1 : ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).base ((inv (𝔓.efib A hA ρ hρ)).base z) =
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base ((𝔓.comp A hA ρ hρ 0).base z) := by
    change ((inv (𝔓.efib A hA ρ hρ)) ≫ 𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst _ _).base z = _
    rw [IsIso.inv_hom_id_assoc, Scheme.Hom.comp_base, TopCat.comp_app]
  have h2 : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base ((𝔓.comp A hA ρ hρ 0).base z) =
      𝔓.εinf.1.base ((Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A))) := by
    rw [hz]
    change (XHDRLevel.sectionFibre 𝔓.εinf ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _).base _ = _
    rw [XHDRLevel.sectionFibre, pullback.lift_fst, Scheme.Hom.comp_base, TopCat.comp_app]
  rw [h1, h2, 𝔓.εinf_chart, Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.image_top_eq_opensRange]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 6400000 in

theorem read_iotaInf_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hne : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))))
    (hne' : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))))
    (b' : ↥(chartAlgInf p (ΓN p M H hpM) hj)) :
    haveI := hne; haveI := hne'
    ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv (𝔓.iotaInf b')))))) =
    ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b'))))) := by
  haveI := hne; haveI := hne'
  have hVle : ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) ≤ 𝔓.π.1 ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤) := by
    rintro x ⟨t, -, rfl⟩
    show (ιInf p (ΓM M H) hj ≫ 𝔓.π.1).base t ∈ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)
    rw [𝔓.pi_chartInf]
    exact ⟨_, trivial, rfl⟩
  have hσ : (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom 𝔓.iotaInf))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv.hom b') =
      (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv.hom (𝔓.iotaInf b') := by
    have h := congrArg (fun ψ => ψ.hom b') (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (AlgHom.toRingHom 𝔓.iotaInf)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  have KEY := ReadChartInf.appLE_appIso_inv_eq (ιInf p (ΓM M H) hj) (ιInf p (ΓN p M H hpM) hj) 𝔓.π.1
    (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom 𝔓.iotaInf))) 𝔓.pi_chartInf hVle
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv.hom b')
  rw [hσ] at KEY
  exact congrArg (𝔓.Mfib A hA ρ hρ).ffEquiv.symm
    (ReadChartInf.germToFunctionField_app_eq_of_appLE_eq _ 𝔓.π.1 _ (efib_fst_eq p M H hpM hj 𝔓 A hA ρ hρ) _ _ hVle _ _ KEY)

end ReadChartInfM

theorem ReadChartInfM.coeffMap_jqModC {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    coeffMap f (jqModC A) = jqModC B := by
  ext n
  rw [coeffMap_coeff, coeff_jqModC_eq_intCast (R := A), coeff_jqModC_eq_intCast (R := B), map_intCast]

set_option maxHeartbeats 12800000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))),
    ∀ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      (((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b))))
          : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by
  refine ⟨ReadChartInfM.nonempty_preimage p M H hpM hj 𝔓 A hA ρ hρ, ?_⟩
  intro y hy
  haveI hne := ReadChartInfM.nonempty_preimage p M H hpM hj 𝔓 A hA ρ hρ
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  haveI : (ΓM M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  have hTM : ModularGroup.T ∈ (ΓM M H) := ModularCurve.translation_mem_GammaH _ _
  haveI : IsLocalRing (R p) := GaloisRep.ratLocalizedAt.isLocalRing (Fact.out : p.Prime)
  have hτp : ((IsLocalRing.residue ↥A).comp ρ) ((p : ℕ) : R p) = 0 := by
    rw [RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa [ValuationSubring.LiesOverPrime] using hA

  have hxN : jqModC (IsLocalRing.ResidueField ↥A) ∈ qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) := by
    have hpin := 𝔓.Mfib_pin A hA ρ hρ (jChartFin p (ΓN p M H hpM) hj) (jqModC ↥A) (by
      rw [ReadChartInfM.coeffMap_jqModC]
      show _ = coeffEmb (AlgebraicClosure ℚ) ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
      rw [coe_jAt, coeffEmb, ReadChartInfM.coeffMap_jqModC])
    rw [ReadChartInfM.coeffMap_jqModC] at hpin
    rw [← hpin]
    exact SetLike.coe_mem _

  obtain ⟨W₀, hW₀, hW₀R, hW₀p, hW₀j, hW₀6⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (ΓM M H) hj
  obtain ⟨hBW, 𝔮, h𝔮, h𝔮pr, hp𝔮, h𝔮min, -, -, -⟩ :=
    ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) hTM p (jAt (ΓM M H) hj) (coe_jAt _ hj) W₀ hW₀

  let rM : ↥(chartAlgInf p (ΓM M H) hj) →+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
    (𝔓.Mfib A hA ρ hρ).ffEquiv.symm.toRingHom.comp
      (((𝔓.Mfib A hA ρ hρ).C.germToFunctionField ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))).hom.comp
        ((((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom.comp
          ((((ιInf p (ΓM M H) hj).appIso ⊤).inv).hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv.hom)))
  have rM_apply : ∀ b' : ↥(chartAlgInf p (ΓM M H) hj), rM b' =
      (𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b')))) := fun _ => rfl
  rw [← rM_apply]

  have hker : ∀ b' : ↥(chartAlgInf p (ΓM M H) hj), rM b' = 0 ↔ b' ∈ 𝔮 := by
    have hP : RingHom.ker rM = 𝔮 := by
      apply le_antisymm
      · intro b' hb'
        exact (h𝔮 b').mpr (ModularCurve.XHDRModelAtP.mem_nonunits_gauss_of_ffEquiv_symm_germToFunctionField_app_comp_zero_eq_zero p M H hpM hpM2 hHp hj 𝔓 A hA ρ hρ W₀ hW₀ hne b' (by rw [← rM_apply]; exact hb'))
      · refine h𝔮min.2 ⟨RingHom.ker_isPrime rM, ?_⟩ ?_
        · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
          apply Subtype.ext
          push_cast
          rw [map_natCast]
          push_cast
          rw [← map_natCast (HahnSeries.C : (IsLocalRing.ResidueField ↥A) →+* LaurentSeries (IsLocalRing.ResidueField ↥A)) p, CharP.cast_eq_zero, map_zero]
        · intro b' hb'
          exact (h𝔮 b').mpr (ModularCurve.XHDRModelAtP.mem_nonunits_gauss_of_ffEquiv_symm_germToFunctionField_app_comp_zero_eq_zero p M H hpM hpM2 hHp hj 𝔓 A hA ρ hρ W₀ hW₀ hne b' (by rw [← rM_apply]; exact hb'))
    intro b'; rw [← hP, RingHom.mem_ker]

  have hkred : ∀ b' : ↥(chartAlgInf p (ΓM M H) hj), ReadChartInfM.red p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ) b' = 0 ↔ b' ∈ 𝔮 := fun b' => by
    rw [h𝔮]
    exact ReadChartInfM.red_eq_zero_iff_mem_nonunits p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ) hτp W₀ hW₀ hW₀R
      (hW₀p _ (Ideal.mem_span_singleton_self _)) hW₀6 b'

  have hredι : ∀ u : ↥(chartAlgInf p (ΓN p M H hpM) hj),
      ReadChartInfM.red p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ) (𝔓.iotaInf u) = ReadChartInfM.red p (ΓN p M H hpM) hj ((IsLocalRing.residue ↥A).comp ρ) u := by
    intro u
    apply ReadChartInfM.red_eq_of_coeffMap_eq
    rw [ReadChartInfM.lift_spec, 𝔓.iotaInf_spec]
  have hreadι : ∀ u : ↥(chartAlgInf p (ΓN p M H hpM) hj),
      ((rM (𝔓.iotaInf u) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = ReadChartInfM.red p (ΓN p M H hpM) hj ((IsLocalRing.residue ↥A).comp ρ) u := by
    intro u
    obtain ⟨hne', hcb⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib p M H hpM hj 𝔓 A hA ρ hρ u
    rw [rM_apply, ReadChartInfM.read_iotaInf_eq p M H hpM hj 𝔓 A hA ρ hρ hne hne' u,
      hcb _ (ReadChartInfM.lift_spec p (ΓN p M H hpM) hj u)]
    rfl

  have hmem := ReadChartInfM.red_mem_adjoin_range_red p hj M H hpM hpM2 hHp A hA ρ hρ ⟨_, hxN⟩ rfl b
  obtain ⟨s, t, ht0, hst⟩ := LaurentSeries.exists_mul_eq_of_mem_adjoin_range_of_coeff_mem_bot p
    (ReadChartInfM.red p (ΓN p M H hpM) hj ((IsLocalRing.residue ↥A).comp ρ))
    (fun u n => by rw [ReadChartInfM.red, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeffMap_coeff]
                   exact GaloisRep.residue_ratLocalizedAt_mem_bot p ρ _)
    _ hmem
    (fun n => by rw [ReadChartInfM.red, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeffMap_coeff]
                 exact GaloisRep.residue_ratLocalizedAt_mem_bot p ρ _)

  have hrel : b * 𝔓.iotaInf t - 𝔓.iotaInf s ∈ 𝔮 := by
    rw [← hkred, map_sub, map_mul, hredι, hredι, hst, sub_self]
  have hrel' : rM b * rM (𝔓.iotaInf t) = rM (𝔓.iotaInf s) := by
    have := (hker _).mpr hrel
    rwa [map_sub, map_mul, sub_eq_zero] at this
  have hcoe := congrArg (fun z : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) => (z : LaurentSeries (IsLocalRing.ResidueField ↥A))) hrel'
  simp only [MulMemClass.coe_mul] at hcoe
  rw [hreadι, hreadι, ← hst] at hcoe
  have hfin : ((rM b : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = ReadChartInfM.red p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ) b :=
    mul_right_cancel₀ ht0 hcoe
  rw [hfin]
  exact ReadChartInfM.red_eq_of_coeffMap_eq p (ΓM M H) hj _ b y hy

end S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd (solution)
