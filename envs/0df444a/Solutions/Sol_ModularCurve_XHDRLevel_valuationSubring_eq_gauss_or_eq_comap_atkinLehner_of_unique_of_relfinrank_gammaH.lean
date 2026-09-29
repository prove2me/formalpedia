-- Prove2me | solution 1 for ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d648b6fb-5cf8-5cea-9135-eb7528769832

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
import Theorems.Thm_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup qExpFunctionFieldC qExpFunctionFieldC_mono qExpand jqModC"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X exists_primesOver_pair_integralClosure_comap_gauss_gammaH"
namespace Gamma3
p2m_open "ModularCurve.XHDRLevel ModularCurve"

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

theorem gammaH_le_gammaH_infSubgroup
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hdvd : M / p ∣ M := Nat.div_dvd_of_dvd hpM
  have hA0' : A ∈ CongruenceSubgroup.Gamma0 (M / p) := by
    have h := CongruenceSubgroup.Gamma0_mem.mp hA0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact CongruenceSubgroup.Gamma0_mem.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((Int.natCast_dvd_natCast.mpr hdvd).trans h))
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', ?_⟩
  refine ⟨CohCarrier.gamma0Units M ⟨A, hA0⟩, hAH, ?_⟩
  apply Units.ext
  rw [ZMod.unitsMap, Units.coe_map]
  show ZMod.castHom hdvd (ZMod (M / p)) ((CohCarrier.gamma0Units M ⟨A, hA0⟩ : ZMod M)) =
    (CohCarrier.gamma0Units (M / p) ⟨A, hA0'⟩ : ZMod (M / p))
  rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  show ZMod.castHom hdvd (ZMod (M / p)) (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) =
    (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p))
  rw [map_intCast]

theorem le_infSubgroup
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) := by

  exact qExpFunctionFieldC_mono ℚ (gammaH_le_gammaH_infSubgroup p M H hpM hHp)

noncomputable def incl (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
  (IntermediateField.inclusion (le_infSubgroup p M H hpM hHp) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))

theorem coe_incl (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) :
    ((incl p M H hpM hHp x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := by
  rw [incl, RingHom.coe_coe]
  exact IntermediateField.coe_inclusion _ x

theorem ringHom_ext_ratLocalizedAt {S : Type*} [CommRing S] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem incl_algebraMap (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) (a : ↥(GaloisRep.ratLocalizedAt p)) :
    incl p M H hpM hHp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a :=
  RingHom.congr_fun (ringHom_ext_ratLocalizedAt p ((incl p M H hpM hHp).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) a

section Count

variable (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
variable (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

def IsBranch {Γ : Subgroup SL(2, ℤ)} (j : ↥(qExpFunctionFieldC ℚ Γ)) (V : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ)) : Prop :=
  (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) a ∈ V) ∧
  (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) a ∈ V.nonunits) ∧
  (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
    Polynomial.aeval j Q ∈ V ∧ (Polynomial.aeval j Q)⁻¹ ∈ V)

theorem isBranch_comap_incl (V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hV : IsBranch p (jAt (CohCarrier.GammaH M H) hj) V) :
    IsBranch p (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) (V.comap (incl p M H hpM hHp)) := by
  obtain ⟨h1, h1', h2⟩ := hV

  have hι : ∀ a : ↥(GaloisRep.ratLocalizedAt p), incl p M H hpM hHp (algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a :=
    incl_algebraMap p M H hpM hHp
  have hιj : incl p M H hpM hHp (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) = jAt (CohCarrier.GammaH M H) hj := by
    apply Subtype.ext
    rw [coe_incl, coe_jAt, coe_jAt]
  have hιQ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p),
      incl p M H hpM hHp (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q) =
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q := by
    intro Q
    have hcomp : (incl p M H hpM hHp).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := RingHom.ext hι
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hιj, hcomp]
  refine ⟨fun a => ?_, fun a ha => ?_, fun Q hQ => ?_⟩
  · rw [ValuationSubring.mem_comap, hι]; exact h1 a
  · rw [ValuationSubring.mem_nonunits_iff_or]
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp (h1' a ha) with h0 | hinv
    · left
      have : incl p M H hpM hHp (algebraMap ↥(GaloisRep.ratLocalizedAt p) _ a) = 0 := by rw [hι, h0]
      exact (map_eq_zero_iff _ (incl p M H hpM hHp).injective).mp this
    · right
      rw [ValuationSubring.mem_comap, map_inv₀, hι]
      exact hinv
  · obtain ⟨hQ1, hQ2⟩ := h2 Q hQ
    refine ⟨?_, ?_⟩
    · rw [ValuationSubring.mem_comap, hιQ]; exact hQ1
    · rw [ValuationSubring.mem_comap, map_inv₀, hιQ]; exact hQ2

scoped instance instDVR_R : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

theorem maximalIdeal_R : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out

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

theorem p_ne_zero_R : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem irreducible_p : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (p_ne_zero_R p) (maximalIdeal_R p)

theorem exists_eq_C_pow_mul_primitive (m : ℕ) : ∀ (a : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) (k : ℕ) (u : ↥(GaloisRep.ratLocalizedAt p)), IsUnit u →
    PowerSeries.coeff k a = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m * u →
    ∃ (n : ℕ) (a'' : PowerSeries ↥(GaloisRep.ratLocalizedAt p)), a''.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      a = (PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ^ n * a'' := by
  induction m with
  | zero =>
    intro a k u hu hk
    refine ⟨0, a, fun h => ?_, by rw [pow_zero, one_mul]⟩
    have hk0 := congrArg (PowerSeries.coeff k) h
    rw [PowerSeries.coeff_map, map_zero, hk, pow_zero, one_mul] at hk0
    exact (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hk0
  | succ m ih =>
    intro a k u hu hk
    by_cases h : a.map (GaloisRep.ratLocalizedAtResidue p) = 0
    · have hdiv : ∀ i, ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ PowerSeries.coeff i a := fun i =>
        (res_eq_zero_iff p _).mp (by have := congrArg (PowerSeries.coeff i) h; rwa [PowerSeries.coeff_map, map_zero] at this)
      choose t ht using hdiv
      have ha : a = PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * PowerSeries.mk t := by
        ext i; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ht i]
      have hk1 : PowerSeries.coeff k (PowerSeries.mk t) = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m * u := by
        rw [PowerSeries.coeff_mk]
        have := ht k
        rw [hk, pow_succ, mul_comm (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m), mul_assoc] at this
        exact (mul_left_cancel₀ (p_ne_zero_R p) this).symm
      obtain ⟨n, a'', h1, h2⟩ := ih (PowerSeries.mk t) k u hu hk1
      exact ⟨n + 1, a'', h1, by rw [ha, h2, pow_succ]; ring⟩
    · exact ⟨0, a, h, by rw [pow_zero, one_mul]⟩

theorem exists_eq_C_pow_mul_primitive' (a : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) (ha : a ≠ 0) :
    ∃ (n : ℕ) (a'' : PowerSeries ↥(GaloisRep.ratLocalizedAt p)), a''.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      a = (PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ^ n * a'' := by
  obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k a ≠ 0 := by
    by_contra h; push Not at h; exact ha (PowerSeries.ext fun k => by rw [h k, map_zero])
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk (irreducible_p p)
  exact exists_eq_C_pow_mul_primitive p m a k v v.isUnit (by rw [hv, mul_comm])

theorem ofPowerSeries_C_pow_mul (n : ℕ) (a'' : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) :
    HahnSeries.ofPowerSeries ℤ ℚ (((PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ^ n * a'').map (GaloisRep.ratLocalizedAt p).subtype) =
      ((p : ℕ) : LaurentSeries ℚ) ^ n * HahnSeries.ofPowerSeries ℤ ℚ (a''.map (GaloisRep.ratLocalizedAt p).subtype) := by
  rw [map_mul, map_pow, PowerSeries.map_C, map_natCast, map_mul, map_pow]
  congr 2
  rw [map_natCast, map_natCast]

theorem exists_eq_pow_mul_unit_of_gaussPin (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (hf : f ≠ 0) :
    ∃ (n : ℤ) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), u ∈ W₀ ∧ u⁻¹ ∈ W₀ ∧
      f = (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ^ n * u := by

  have hpF : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = (p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := map_natCast _ p
  have hpL : (((p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) := by push_cast; rfl
  have hp0 : (p : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) p]
    exact fun h => (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0) (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))
  have hp0F : (p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hprim : ∀ b : PowerSeries ↥(GaloisRep.ratLocalizedAt p), b.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      HahnSeries.ofPowerSeries ℤ ℚ (b.map (GaloisRep.ratLocalizedAt p).subtype) ≠ 0 := by
    intro b hb h0
    apply hb
    have hinj : Function.Injective (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype) :=
      PowerSeries.map_injective _ Subtype.val_injective
    have h1 : PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b = 0 :=
      HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have : b = 0 := hinj (h1.trans (map_zero _).symm)
    rw [this, map_zero]

  have key : ∀ g : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), g ≠ 0 → g ∈ W₀ → ∃ (n : ℤ) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), u ∈ W₀ ∧ u⁻¹ ∈ W₀ ∧
      g = (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ^ n * u := by
    intro g hg hgW
    obtain ⟨a, a', ha', h⟩ := (hW₀ g).mp hgW
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero, map_zero, mul_eq_zero] at h
      rcases h with h | h
      · exact hg (by exact_mod_cast h)
      · exact hprim a' ha' h
    obtain ⟨n, a'', ha'', haa⟩ := exists_eq_C_pow_mul_primitive' p a ha0
    refine ⟨n, g * ((p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ^ n)⁻¹, ?_, ?_, ?_⟩
    · rw [hW₀]
      refine ⟨a'', a', ha', ?_⟩
      push_cast
      rw [mul_right_comm, h, haa, ofPowerSeries_C_pow_mul, mul_comm (((p : ℕ) : LaurentSeries ℚ) ^ n),
        mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), mul_one]
    · rw [hW₀]
      refine ⟨a', a'', ha'', ?_⟩
      have hgL : ((g : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) ≠ 0 := by exact_mod_cast hg
      push_cast
      have e1 : ((g : LaurentSeries ℚ) * ((p : LaurentSeries ℚ) ^ n)⁻¹)⁻¹ = (p : LaurentSeries ℚ) ^ n * (g : LaurentSeries ℚ)⁻¹ := by
        rw [mul_inv, inv_inv, mul_comm]
      rw [e1]
      have e2 : HahnSeries.ofPowerSeries ℤ ℚ (a''.map (GaloisRep.ratLocalizedAt p).subtype) =
          ((p : LaurentSeries ℚ) ^ n)⁻¹ * ((g : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype)) := by
        rw [h, haa, ofPowerSeries_C_pow_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
      rw [e2]
      field_simp
    · rw [hpF, zpow_natCast, mul_comm, inv_mul_cancel_right₀ (pow_ne_zero _ hp0F)]
  rcases W₀.mem_or_inv_mem f with hfW | hfW
  · exact key f hf hfW
  · obtain ⟨n, u, hu, hu', h⟩ := key f⁻¹ (inv_ne_zero hf) hfW
    refine ⟨-n, u⁻¹, hu', by rw [inv_inv]; exact hu, ?_⟩
    have := congrArg (·⁻¹) h
    simp only [inv_inv, mul_inv, ← zpow_neg] at this
    exact this

end Count

end ModularCurve.XHDRLevel.Gamma3
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve.XHDRLevel.Gamma3"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve"

open _root_.ModularCurve.XHDRLevel _root_.P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.ModularCurve.XHDRLevel in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
        (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
          ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))

    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (W₀).nonunits)
    (hW₀₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ W₀)
    (hW₀₆ : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (W₀).nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀)

    (hW₁₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (W₀.comap σ.toAlgHom.toRingHom))
    (hW₁₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ ((W₀.comap σ.toAlgHom.toRingHom)).nonunits)
    (hW₁₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (W₀.comap σ.toAlgHom.toRingHom) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (W₀.comap σ.toAlgHom.toRingHom))
    (hW₁₆ : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ ((W₀.comap σ.toAlgHom.toRingHom)).nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ (W₀.comap σ.toAlgHom.toRingHom))
    (hne : (W₀.comap σ.toAlgHom.toRingHom) ≠ W₀)

    (huniq : ∀ V V' : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ V) →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ (V).nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q)⁻¹ ∈ V) →
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ V') →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ (V').nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q ∈ V' ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q)⁻¹ ∈ V') →
        V = V')

    (hdeg : IntermediateField.relfinrank (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = p + 1)

    (V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hV₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V)
    (hV₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits)
    (hV₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) :
    V = W₀ ∨ V = W₀.comap σ.toAlgHom.toRingHom := by
  classical
  haveI hpr : Fact p.Prime := inferInstance
  have hp : p.Prime := Fact.out

  have hAB : qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤
      qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) := Gamma3.le_infSubgroup p M H hpM hHp
  let ι : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := Gamma3.incl p M H hpM hHp

  let V' : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := W₀.comap ι
  letI algEL : Algebra ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := ι.toAlgebra
  letI algOL : Algebra ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (ι.comp V'.subtype).toAlgebra
  haveI : IsScalarTower ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hV'b := Gamma3.isBranch_comap_incl p M H hpM hHp hj W₀ ⟨hW₀₁, hW₀₁', hW₀₂⟩
  have hPF : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    rw [Gamma3.ringHom_ext_ratLocalizedAt p (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
      ((algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).comp (GaloisRep.ratLocalizedAt p).subtype)]
    exact (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).injective.comp Subtype.val_injective
  have hP0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 :=
    (map_ne_zero_iff _ hPF).mpr (by exact_mod_cast hp.ne_zero)
  have hnuV : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))), x ∈ V'.nonunits → ι x ∈ W₀.nonunits := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff_or] at hx ⊢
    rcases hx with h | h
    · left; rw [h, map_zero]
    · right; rw [← map_inv₀]; exact fun hm => h (ValuationSubring.mem_comap.mpr hm)
  haveI hDVR : IsDiscreteValuationRing ↥V' := by

    let ϖ : ↥V' := ⟨algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)), hV'b.1 _⟩
    have hιϖ : ι (ϖ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := Gamma3.incl_algebraMap p M H hpM hHp _
    have hϖnu : (ϖ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ V'.nonunits := hV'b.2.1 _ (Ideal.mem_span_singleton_self _)
    have hϖ0 : (ϖ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ≠ 0 := fun h => hP0 (by rw [← hιϖ, h, map_zero])
    have hPnu : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ W₀.nonunits := hW₀₁' _ (Ideal.mem_span_singleton_self _)
    have hPinv : (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∉ W₀ := by
      rcases (ValuationSubring.mem_nonunits_iff_or _).mp hPnu with h | h
      · exact absurd h hP0
      · exact h

    have hunit : ∀ y : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))), y ≠ 0 → ι y ∈ W₀ → (ι y)⁻¹ ∈ W₀ → ∃ v : (↥V')ˣ, ((v : ↥V') : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) = y := by
      intro y hy h1 h2
      have hy1 : y ∈ V' := ValuationSubring.mem_comap.mpr h1
      have hy2 : y⁻¹ ∈ V' := ValuationSubring.mem_comap.mpr (by rw [map_inv₀]; exact h2)
      refine ⟨⟨⟨y, hy1⟩, ⟨y⁻¹, hy2⟩, Subtype.ext (mul_inv_cancel₀ hy), Subtype.ext (inv_mul_cancel₀ hy)⟩, rfl⟩
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, ?_, ?_⟩
    ·
      refine irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩
      · exact (IsLocalRing.notMem_maximalIdeal.mpr hu) (ValuationSubring.coe_mem_nonunits_iff.mp hϖnu)
      · by_contra hab'
        rw [not_or] at hab'
        have ha : (a : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ V'.nonunits :=
          ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hab'.1))
        have hb : (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ V'.nonunits :=
          ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hab'.2))
        have ha' := hW₀₆ _ (hnuV _ ha)
        have hb' := hW₀₆ _ (hnuV _ hb)
        have hprod := W₀.mul_mem _ _ ha' hb'
        have hιab : ι (a : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) * ι (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := by
          rw [← map_mul, ← hιϖ]
          exact congrArg ι (congrArg Subtype.val hab).symm
        apply hPinv
        have e : ι (a : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ *
            (ι (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹) =
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ := by
          rw [mul_mul_mul_comm, hιab, mul_inv_cancel_left₀ hP0]
        rw [e] at hprod
        exact hprod
    ·
      intro x hx
      have hx0 : (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ≠ 0 := fun h => hx (Subtype.ext h)
      have hg0 : ι (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ≠ 0 := (map_ne_zero_iff _ ι.injective).mpr hx0
      have hgW : ι (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ W₀ := ValuationSubring.mem_comap.mp x.2
      obtain ⟨n, u, hu, hu', hg⟩ := Gamma3.exists_eq_pow_mul_unit_of_gaussPin p M H W₀ hW₀ _ hg0
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      ·
        refine ⟨m, ?_⟩
        set y : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) * ((ϖ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ^ m)⁻¹ with hy
        have hιy : ι y = u := by
          rw [hy, map_mul, map_inv₀, map_pow, hιϖ, hg, zpow_natCast, mul_comm, inv_mul_cancel_left₀ (pow_ne_zero _ hP0)]
        have hy0 : y ≠ 0 := mul_ne_zero hx0 (inv_ne_zero (pow_ne_zero _ hϖ0))
        obtain ⟨v, hv⟩ := hunit y hy0 (hιy ▸ hu) (hιy ▸ hu')
        refine ⟨v, Subtype.ext ?_⟩
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hv, hy, ← mul_assoc, mul_comm ((ϖ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ^ m), mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hϖ0), mul_one]
      ·
        refine ⟨0, ?_⟩
        have hinvW : (ι (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))))⁻¹ ∈ W₀ := by
          have : (ι (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))))⁻¹ = (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ^ (m : ℤ) * u⁻¹ := by
            rw [hg, mul_inv, ← zpow_neg, neg_neg]
          rw [this, zpow_natCast]
          exact W₀.mul_mem _ _ (W₀.toSubring.pow_mem (hW₀₁ _) m) hu'
        obtain ⟨v, hv⟩ := hunit (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) hx0 hgW hinvW
        refine ⟨v, ?_⟩
        rw [pow_zero, one_mul]
        exact Subtype.ext hv

  have hrank : Module.finrank ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = p + 1 := by
    rw [← hdeg, IntermediateField.relfinrank_eq_finrank_of_le hAB]
    refine (LinearEquiv.finrank_eq ?_).symm
    exact
      { toFun := fun x => ⟨(x : LaurentSeries ℚ), (IntermediateField.mem_extendScalars hAB).mp x.2⟩
        map_add' := fun x y => by
          apply Subtype.ext
          simp only [AddMemClass.coe_add]
        map_smul' := fun a x => by
          apply Subtype.ext
          rw [RingHom.id_apply, IntermediateField.coe_smul, Algebra.smul_def, IntermediateField.algebraMap_apply,
            Algebra.smul_def, RingHom.algebraMap_toAlgebra, MulMemClass.coe_mul, Gamma3.coe_incl]
        invFun := fun y => ⟨(y : LaurentSeries ℚ), (IntermediateField.mem_extendScalars hAB).mpr y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  haveI hfd : FiniteDimensional ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := Module.finite_of_finrank_pos (by rw [hrank]; omega)
  haveI hsep : Algebra.IsSeparable ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := inferInstance
  haveI : FaithfulSMul ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (faithfulSMul_iff_algebraMap_injective ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).mpr
    (ι.injective.comp Subtype.val_injective)

  haveI hDD : IsDedekindDomain ↥(integralClosure ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    IsIntegralClosure.isDedekindDomain ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _
  haveI hMF : Module.Finite ↥V' ↥(integralClosure ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    IsIntegralClosure.finite ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _
  haveI hFR : IsFractionRing ↥(integralClosure ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _

  set W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := W₀.comap σ.toAlgHom.toRingHom with hW₁
  have hW₀b : Gamma3.IsBranch p (jAt (CohCarrier.GammaH M H) hj) W₀ := ⟨hW₀₁, hW₀₁', hW₀₂⟩
  have hW₁b : Gamma3.IsBranch p (jAt (CohCarrier.GammaH M H) hj) W₁ := ⟨hW₁₁, hW₁₁', hW₁₂⟩
  have hVb : Gamma3.IsBranch p (jAt (CohCarrier.GammaH M H) hj) V := ⟨hV₁, hV₁', hV₂⟩
  have hpR0 : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hinjR : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    rw [Gamma3.ringHom_ext_ratLocalizedAt p (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
      ((algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).comp (GaloisRep.ratLocalizedAt p).subtype)]
    exact (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).injective.comp Subtype.val_injective
  have hpF0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := (map_ne_zero_iff _ hinjR).mpr hpR0
  have hW₀b' := Gamma3.isBranch_comap_incl p M H hpM hHp hj W₀ ⟨hW₀₁, hW₀₁', hW₀₂⟩
  have hdom : ∀ U : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), Gamma3.IsBranch p (jAt (CohCarrier.GammaH M H) hj) U →
      U ≠ ⊤ ∧ (∀ x : ↥V', algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) x ∈ U) ∧
        (∀ x ∈ IsLocalRing.maximalIdeal ↥V', algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) x ∈ U.nonunits) := by
    intro U hU
    have hUb := Gamma3.isBranch_comap_incl p M H hpM hHp hj U hU
    have hUV : U.comap ι = V' := huniq _ _ hUb.1 hUb.2.1 hUb.2.2 hW₀b'.1 hW₀b'.2.1 hW₀b'.2.2
    refine ⟨?_, fun x => ?_, fun x hx => ?_⟩
    · intro hT
      have hpn := hU.2.1 _ (Ideal.mem_span_singleton_self _)
      rw [hT, ValuationSubring.mem_nonunits_iff_or] at hpn
      rcases hpn with h | h
      · exact hpF0 h
      · exact h (ValuationSubring.mem_top _)
    · have hx : (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ U.comap ι := by rw [hUV]; exact x.2
      exact ValuationSubring.mem_comap.mp hx
    · have hx' : ((x : ↥V') : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ (U.comap ι).nonunits := by
        rw [hUV]; exact ValuationSubring.coe_mem_nonunits_iff.mpr hx
      show ι (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ U.nonunits
      rw [ValuationSubring.mem_nonunits_iff_or] at hx' ⊢
      rcases hx' with h | h
      · left; rw [h, map_zero]
      · right; rw [← map_inv₀]; exact fun hm => h (ValuationSubring.mem_comap.mpr hm)

  obtain ⟨𝔓₀, 𝔓₁, hP0, hP1, h00, h10, hne𝔓, hov0, hov1, hf0, hf1⟩ :=
    exists_primesOver_pair_integralClosure_comap_gauss_gammaH p M H hpM hpM2 hHp hj hAB σ hσ W₀ hW₀
      hW₀₁ hW₀₁' hW₀₂ hW₀₆ hW₁₁ hW₁₁' hW₁₂ hW₁₆ hne
  let 𝔓 : Fin 2 → Ideal ↥(integralClosure ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := ![𝔓₀, 𝔓₁]
  haveI hprime : ∀ i, (𝔓 i).IsPrime := fun i => by fin_cases i <;> assumption
  have h0 : ∀ i, 𝔓 i ≠ ⊥ := fun i => by fin_cases i <;> assumption
  haveI hover : ∀ i, (𝔓 i).LiesOver (IsLocalRing.maximalIdeal ↥V') := fun i => by fin_cases i <;> assumption
  have hinj : Function.Injective 𝔓 := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hne𝔓
    · exact absurd h.symm hne𝔓
    · rfl
  let d : Fin 2 → ℕ := ![1, p]
  have hd : ∀ i, d i ≤ (IsLocalRing.maximalIdeal ↥V').inertiaDeg' (𝔓 i) := fun i => by
    fin_cases i
    · exact hf0
    · exact hf1
  have hsum : Module.finrank ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≤ ∑ i, d i := by
    rw [hrank, Fin.sum_univ_two]
    show p + 1 ≤ 1 + p
    omega

  obtain ⟨-, -, -, -, hclass, -⟩ :=
    IsDiscreteValuationRing.primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
      (O := ↥V') (F := ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) 𝔓 h0 hinj d hd hsum

  obtain ⟨i₀, hi₀⟩ := hclass W₀ (hdom W₀ hW₀b).1 (hdom W₀ hW₀b).2.1 (hdom W₀ hW₀b).2.2
  obtain ⟨i₁, hi₁⟩ := hclass W₁ (hdom W₁ hW₁b).1 (hdom W₁ hW₁b).2.1 (hdom W₁ hW₁b).2.2
  obtain ⟨iV, hiV⟩ := hclass V (hdom V hVb).1 (hdom V hVb).2.1 (hdom V hVb).2.2

  have hne' : W₀ ≠ W₁ := fun h => hne h.symm
  have hi : i₀ ≠ i₁ := fun h => hne' (hi₀.trans (h ▸ hi₁.symm))
  have hcases : iV = i₀ ∨ iV = i₁ := by
    revert hi; fin_cases iV <;> fin_cases i₀ <;> fin_cases i₁ <;> simp
  rcases hcases with h | h
  · left; rw [hiV, h, ← hi₀]
  · right; rw [hiV, h, ← hi₁]

end S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH (solution)
