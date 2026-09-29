-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.mem_gauss_and_isPrime_map_span_of_mem_range_comp_zero_of_not_mem_range_comp_one_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ebb6bc82-0967-5e1e-9a3d-e34bff0e698f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le
import Theorems.Thm_ModularCurve_XHDRLevel_isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_mem_gauss_and_isPrime_map_span_of_mem_range_comp_zero_of_not_mem_range_comp_one_chartAlgInf
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

namespace OneCompPrimeInf

open IsLocalRing

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

omit [Fact p.Prime] [NeZero M] in

theorem natCast_mem_of_iotaInf_eq_fst
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A)
    (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (𝔭 : PrimeSpectrum ↥(chartAlgInf p (ΓM M H) hj))
    (h𝔭y : (ιInf p (ΓM M H) hj).base 𝔭 =
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y) :
    algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) ((p : ℕ) : R p) ∈ 𝔭.asIdeal := by

  have h1 : (toBase p (ΓM M H) hj).base ((ιInf p (ΓM M H) hj).base 𝔭) =
      PrimeSpectrum.comap (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) 𝔭 := by
    rw [← Scheme.Hom.comp_apply, AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase]
    rfl
  have h2 : (toBase p (ΓM M H) hj).base ((ιInf p (ΓM M H) hj).base 𝔭) =
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))).base ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y) := by
    rw [h𝔭y, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have h3 : ((Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))).base
      ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y)).asIdeal = RingHom.ker ((IsLocalRing.residue ↥A).comp ρ) := by
    set z := (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y
    have hz : z.asIdeal = ⊥ := by
      haveI : z.asIdeal.IsPrime := z.isPrime
      exact (Ideal.eq_bot_of_prime z.asIdeal)
    show (PrimeSpectrum.comap ((IsLocalRing.residue ↥A).comp ρ) z).asIdeal = RingHom.ker ((IsLocalRing.residue ↥A).comp ρ)
    rw [PrimeSpectrum.comap_asIdeal, hz, ← RingHom.ker_eq_comap_bot]
  have hp : ((IsLocalRing.residue ↥A).comp ρ) ((p : ℕ) : R p) = 0 := by
    rw [RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact hA
  have key : (PrimeSpectrum.comap (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) 𝔭).asIdeal = RingHom.ker ((IsLocalRing.residue ↥A).comp ρ) := by
    rw [← h1, h2, h3]
  have : ((p : ℕ) : R p) ∈ (PrimeSpectrum.comap (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) 𝔭).asIdeal := by
    rw [key]; exact hp
  rwa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at this

end OneCompPrimeInf

open OneCompPrimeInf in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hW₀ : (∀ f₀ : ↥(qExpFunctionFieldC ℚ (ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hy0 : y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base) (hy1 : y ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (𝔭 : PrimeSpectrum ↥(chartAlgInf p (ΓM M H) hj))
    (h𝔭y : (ιInf p (ΓM M H) hj).base 𝔭 =
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y) :
    algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) ((p : ℕ) : R p) ∈ 𝔭.asIdeal ∧
    (∀ s : ↥(chartAlgInf p (ΓM M H) hj), s ∉ 𝔭.asIdeal → ((s : ↥(qExpFunctionFieldC ℚ (ΓM M H))))⁻¹ ∈ W₀) ∧
    (Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) (Localization.AtPrime 𝔭.asIdeal))
      (Ideal.span {algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) ((p : ℕ) : R p)})).IsPrime := by
  classical
  obtain ⟨P, hPmin, hne, hall, horient, hdict⟩ :=
    ModularCurve.XHDRModelAtP.exists_minimalPrimes_chartAlgInf_eq_pair_and_mem_iff_gauss_and_mem_range_comp_iff_le p M H hpM hpM2 hHp hj 𝔛 W₀ hW₀
  have hP0 : P 0 ≤ 𝔭.asIdeal := (hdict A hA ρ hρ 0 y 𝔭 h𝔭y.symm).mp hy0
  have hP1 : ¬ P 1 ≤ 𝔭.asIdeal := fun h => hy1 ((hdict A hA ρ hρ 1 y 𝔭 h𝔭y.symm).mpr h)
  refine ⟨natCast_mem_of_iotaInf_eq_fst p M H hj A hA ρ y 𝔭 h𝔭y, ?_, ?_⟩
  ·
    intro s hs
    have hs0 : s ∉ P 0 := fun h => hs (hP0 h)
    have hv : ¬ W₀.valuation ((s : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) < 1 := by
      rw [← ValuationSubring.mem_nonunits_iff, ← horient]; exact hs0
    rw [← W₀.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ (not_lt.mp hv)
  ·
    have hred : IsReduced (↥(chartAlgInf p (ΓM M H) hj) ⧸ Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}) :=
      (ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH p M H hpM hpM2 hHp hj).2
    have hrad : (Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))}).IsRadical :=
      (Ideal.isRadical_iff_quotient_reduced _).mpr hred
    have hspan : Ideal.span {((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj))} = P 0 ⊓ P 1 := by
      rw [← hrad.radical, ← Ideal.sInf_minimalPrimes, hall, sInf_insert, sInf_singleton]
    have hpA : algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj) ((p : ℕ) : R p) = ((p : ℕ) : ↥(chartAlgInf p (ΓM M H) hj)) := map_natCast _ _
    rw [hpA, hspan]

    haveI hP0p : (P 0).IsPrime := (hPmin 0).1.1
    set S := Localization.AtPrime 𝔭.asIdeal
    obtain ⟨t, ht1, ht𝔭⟩ := Set.not_subset.mp hP1
    have htop : Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 1) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ht1)
        (IsLocalization.map_units S (⟨t, ht𝔭⟩ : 𝔭.asIdeal.primeCompl))
    have heq : Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 0 ⊓ P 1) = Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 0) := by
      apply le_antisymm (Ideal.map_mono inf_le_left)
      calc Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 0)
          = Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 0) * Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 1) := by rw [htop, Ideal.mul_top]
        _ = Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 0 * P 1) := (Ideal.map_mul _ _ _).symm
        _ ≤ Ideal.map (algebraMap ↥(chartAlgInf p (ΓM M H) hj) S) (P 0 ⊓ P 1) := Ideal.map_mono Ideal.mul_le_inf
    rw [heq]
    exact IsLocalization.isPrime_of_isPrime_disjoint 𝔭.asIdeal.primeCompl S (P 0) hP0p
      (Set.disjoint_left.mpr fun a ha hmem => ha (hP0 hmem))

end S_ModularCurve_XHDRModelAtP_mem_gauss_and_isPrime_map_span_of_mem_range_comp_zero_of_not_mem_range_comp_one_chartAlgInf
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_mem_gauss_and_isPrime_map_span_of_mem_range_comp_zero_of_not_mem_range_comp_one_chartAlgInf (solution)
