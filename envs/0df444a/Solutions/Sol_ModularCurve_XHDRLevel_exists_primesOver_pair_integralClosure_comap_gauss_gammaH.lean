-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_primesOver_pair_integralClosure_comap_gauss_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/31803e21-7a2d-56ab-8732-69bc163fd4d2

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd
import Theorems.Thm_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_injective jNum qExpand_ofPowerSeries_eq_expand jqModC order_qExpandC order_jqModC_def jqModC_ne_zero_def XHDRLevel.valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one"
namespace XHDRLevel
p2m_export "ModularCurve.XHDRLevel" "R jAt coe_jAt X valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one"
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
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve"

namespace AlgVert

open IsLocalRing IsDedekindDomain

section Setup

variable {O : Type*} [CommRing O] [IsDomain O]
  {F : Type*} [Field F] [Algebra O F]

theorem mem_of_isIntegral (V : ValuationSubring F) (hOV : ∀ x : O, algebraMap O F x ∈ V)
    {y : F} (hy : IsIntegral O y) : y ∈ V := by
  let φ : O →+* ↥V := (algebraMap O F).codRestrict V.toSubring hOV
  have hy' : IsIntegral ↥V y := by
    obtain ⟨p, hp, hpy⟩ := hy
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpy
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := F)).mp hy'
  rw [← hz]
  exact z.2

variable (V : ValuationSubring F) (hOV : ∀ x : O, algebraMap O F x ∈ V)

noncomputable def toV : ↥(integralClosure O F) →+* ↥V :=
  (algebraMap (↥(integralClosure O F)) F).codRestrict V.toSubring
    (fun b => mem_of_isIntegral V hOV b.2)

@[scoped simp] theorem coe_toV (b : ↥(integralClosure O F)) : ((toV V hOV b : ↥V) : F) = (b : F) := rfl

noncomputable def centre : Ideal ↥(integralClosure O F) := (maximalIdeal ↥V).comap (toV V hOV)

scoped instance isPrime_centre : (centre V hOV).IsPrime := Ideal.comap_isPrime _ _

theorem mem_centre_iff (b : ↥(integralClosure O F)) : b ∈ centre V hOV ↔ (b : F) ∈ V.nonunits := by
  rw [centre, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toV]

end Setup
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3"

section VS
variable {F : Type*} [Field F]

theorem mem_valuationSubringAtPrime_iff' {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    (v : HeightOneSpectrum B) (x : F) :
    x ∈ HeightOneSpectrum.valuationSubringAtPrime F v ↔ ∃ a s : B, s ∉ v.asIdeal ∧ x * algebraMap B F s = algebraMap B F a := by
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    refine ⟨a, s, hs, ?_⟩
    have hs0 : algebraMap B F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ v.asIdeal.zero_mem)))
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  · rintro ⟨a, s, hs, hx⟩
    have hs0 : algebraMap B F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ v.asIdeal.zero_mem)))
    refine ⟨a, s, hs, ?_⟩
    rw [← hx, mul_assoc, mul_inv_cancel₀ hs0, mul_one]

end VS
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3"

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]

theorem instances_B (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] :
    IsDedekindDomain ↥(integralClosure O F) ∧ Module.Finite O ↥(integralClosure O F) ∧
      IsFractionRing ↥(integralClosure O F) F :=
  ⟨integralClosure.isDedekindDomain O E F, IsIntegralClosure.finite O E F ↥(integralClosure O F),
    IsIntegralClosure.isFractionRing_of_finite_extension O E F ↥(integralClosure O F)⟩

scoped instance faithfulSMul_B : FaithfulSMul O ↥(integralClosure O F) :=
  (faithfulSMul_iff_algebraMap_injective O ↥(integralClosure O F)).mpr
    (fun a b h => FaithfulSMul.algebraMap_injective O F (congrArg Subtype.val h))

variable (V : ValuationSubring F) (hOV : ∀ x : O, algebraMap O F x ∈ V)
  (hdom : ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ V.nonunits)

include hdom in

theorem comap_centre : (centre V hOV).comap (algebraMap O ↥(integralClosure O F)) = maximalIdeal O := by
  ext x
  rw [Ideal.mem_comap, mem_centre_iff]
  constructor
  · intro hx
    by_contra hx'
    have hu : IsUnit x := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hx'
    obtain ⟨u, rfl⟩ := hu
    have hmem : ((algebraMap O ↥(integralClosure O F) ↑u : ↥(integralClosure O F)) : F) ∈ V.nonunits := hx
    have hcoe : ((algebraMap O ↥(integralClosure O F) ↑u : ↥(integralClosure O F)) : F) = algebraMap O F ↑u := rfl
    rw [hcoe] at hmem

    have hunit : IsUnit (⟨algebraMap O F ↑u, hOV ↑u⟩ : ↥V) :=
      (Units.map ((algebraMap O F).codRestrict V.toSubring hOV : O →* ↥V) u).isUnit
    have hmem' := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨algebraMap O F ↑u, hOV ↑u⟩)).mp hmem
    exact (mem_nonunits_iff.mp (mem_maximalIdeal _ |>.mp hmem')) hunit
  · intro hx
    exact hdom x hx

include hdom in
theorem liesOver_centre : (centre V hOV).LiesOver (maximalIdeal O) :=
  ⟨(comap_centre V hOV hdom).symm⟩

include hdom in
theorem centre_ne_bot : centre V hOV ≠ ⊥ := by
  intro h
  have h1 := comap_centre V hOV hdom
  rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O ↥(integralClosure O F))] at h1
  exact IsDiscreteValuationRing.not_a_field O h1.symm

noncomputable def centreHOS [IsDedekindDomain ↥(integralClosure O F)] (h0 : centre V hOV ≠ ⊥) :
    HeightOneSpectrum ↥(integralClosure O F) :=
  ⟨centre V hOV, inferInstance, h0⟩

theorem valuationSubringAtPrime_le [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    (h0 : centre V hOV ≠ ⊥) :
    HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0) ≤ V := by
  rintro x ⟨a, s, hs, rfl⟩
  have ha : ((a : ↥(integralClosure O F)) : F) ∈ V := mem_of_isIntegral V hOV a.2
  have hs' : ((s : ↥(integralClosure O F)) : F) ∉ V.nonunits := fun h => hs ((mem_centre_iff V hOV s).mpr h)
  rw [ValuationSubring.mem_nonunits_iff_or, not_or] at hs'
  exact V.mul_mem _ _ ha (not_not.mp hs'.2)

theorem eq_valuationSubringAtPrime [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    (hV : V ≠ ⊤) (h0 : centre V hOV ≠ ⊥) :
    HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0) = V :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le V hOV h0) hV

include hdom in
theorem card_le_inertiaDeg [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    {ι : Type*} [Fintype ι] (b : ι → F) (hb : ∀ i, IsIntegral O (b i))
    (hres : ∀ c : ι → O, (∑ i, algebraMap O F (c i) * b i) ∈ V.nonunits → ∀ i, c i ∈ maximalIdeal O) :
    Fintype.card ι ≤ (maximalIdeal O).inertiaDeg' (centre V hOV) := by
  classical
  haveI := liesOver_centre V hOV hdom
  rw [Ideal.inertiaDeg_algebraMap]
  let b' : ι → ↥(integralClosure O F) ⧸ centre V hOV := fun i => Ideal.Quotient.mk _ ⟨b i, hb i⟩
  have hli : LinearIndependent (O ⧸ maximalIdeal O) b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨c, hc⟩ : ∃ c : ι → O, ∀ i, Ideal.Quotient.mk (maximalIdeal O) (c i) = g i :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (g i)).choose, fun i => (Ideal.Quotient.mk_surjective (g i)).choose_spec⟩
    have hsum : (Ideal.Quotient.mk (centre V hOV)) (∑ j, algebraMap O ↥(integralClosure O F) (c j) * ⟨b j, hb j⟩) = 0 := by
      rw [map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← hc j, map_mul, Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.algebraMap_eq, Algebra.smul_def,
        IsScalarTower.algebraMap_apply O (O ⧸ maximalIdeal O) (↥(integralClosure O F) ⧸ centre V hOV)]
      rfl
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_centre_iff] at hsum
    have hcoe : ((∑ j, algebraMap O ↥(integralClosure O F) (c j) * ⟨b j, hb j⟩ : ↥(integralClosure O F)) : F)
        = ∑ j, algebraMap O F (c j) * b j := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rfl
    rw [hcoe] at hsum
    have := hres c hsum i
    rw [← hc i, Ideal.Quotient.eq_zero_iff_mem]
    exact this
  exact hli.fintype_card_le_finrank

include hdom in

include hdom in

theorem card_le_inertiaDeg_of_mem [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    [IsFractionRing ↥(integralClosure O F) F] (hV : V ≠ ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → F) (hy : ∀ i, y i ∈ V)
    (hres : ∀ c : ι → O, (∑ i, algebraMap O F (c i) * y i) ∈ V.nonunits → ∀ i, c i ∈ maximalIdeal O) :
    Fintype.card ι ≤ (maximalIdeal O).inertiaDeg' (centre V hOV) := by
  classical
  have h0 := centre_ne_bot V hOV hdom
  have hVW := eq_valuationSubringAtPrime V hOV hV h0

  have hpres : ∀ i, ∃ a s : ↥(integralClosure O F), s ∉ centre V hOV ∧ y i * (s : F) = (a : F) := by
    intro i
    have : y i ∈ HeightOneSpectrum.valuationSubringAtPrime F (centreHOS V hOV h0) := by rw [hVW]; exact hy i
    exact (mem_valuationSubringAtPrime_iff' _ _).mp this
  choose a s hs has using hpres
  let S : ↥(integralClosure O F) := ∏ i, s i
  have hS : S ∉ centre V hOV := by
    intro h
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := centre V hOV)).mp h
    exact hs i hi
  have hSunit : (S : F) ∉ V.nonunits := fun h => hS ((mem_centre_iff V hOV S).mpr h)
  have hSV : (S : F) ∈ V := mem_of_isIntegral V hOV S.2

  let b : ι → F := fun i => y i * (S : F)
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    have e : b i = ((a i * ∏ j ∈ Finset.univ.erase i, s j : ↥(integralClosure O F)) : F) := by
      show y i * ((∏ j, s j : ↥(integralClosure O F)) : F) = _
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]
      push_cast
      rw [← mul_assoc, has i]
    rw [e]
    exact (a i * ∏ j ∈ Finset.univ.erase i, s j).2
  refine card_le_inertiaDeg V hOV hdom b hb (fun c hc i => hres c ?_ i)

  have hsum : (∑ i, algebraMap O F (c i) * b i) = (∑ i, algebraMap O F (c i) * y i) * (S : F) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    show algebraMap O F (c i) * (y i * (S : F)) = _
    ring
  rw [hsum] at hc
  rw [ValuationSubring.mem_nonunits_iff] at hc hSunit ⊢
  rw [map_mul] at hc
  have hS1 : V.valuation (S : F) = 1 := le_antisymm ((V.valuation_le_one_iff _).mpr hSV) (not_lt.mp hSunit)
  rwa [hS1, mul_one] at hc

end Main
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3"

namespace Several

open IsLocalRing IsDedekindDomain

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]

theorem centre_injective [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    {ι : Type*} (V : ι → ValuationSubring F) (hV : ∀ i, V i ≠ ⊤) (hOV : ∀ i, ∀ x : O, algebraMap O F x ∈ V i)
    (hdom : ∀ i, ∀ x ∈ maximalIdeal O, algebraMap O F x ∈ (V i).nonunits)
    (hinj : Function.Injective V) :
    Function.Injective (fun i => centre (V i) (hOV i)) := by
  intro i j h
  apply hinj
  have hi := eq_valuationSubringAtPrime (V i) (hOV i) (hV i) (centre_ne_bot (V i) (hOV i) (hdom i))
  have hj := eq_valuationSubringAtPrime (V j) (hOV j) (hV j) (centre_ne_bot (V j) (hOV j) (hdom j))
  rw [← hi, ← hj]
  congr 1
  exact HeightOneSpectrum.ext h

end Several
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3"

end AlgVert
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3 P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.AlgVert"

namespace Gamma3aOrd

theorem eq_zero_of_sum_mul_pow_eq_zero {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime]
    (J : LaurentSeries K) (hJ0 : J ≠ 0) (hJ : J.order = -1)
    (r : Fin p → LaurentSeries K) (hr : ∀ i, r i = 0 ∨ (p : ℤ) ∣ (r i).order)
    (hsum : ∑ i, r i * J ^ (i : ℕ) = 0) : ∀ i, r i = 0 := by
  classical
  have hJpow : ∀ n : ℕ, (J ^ n).order = -(n : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hJ0) hJ0, ih, hJ]
      push_cast; ring
  by_contra hne
  push Not at hne
  set S : Finset (Fin p) := Finset.univ.filter fun i => r i ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩⟩
  let o : Fin p → ℤ := fun i => (r i).order - (i : ℕ)
  have horder : ∀ i ∈ S, (r i * J ^ (i : ℕ)).order = o i := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    rw [HahnSeries.order_mul hi.2 (pow_ne_zero _ hJ0), hJpow]
    ring

  have hdist : ∀ i ∈ S, ∀ i' ∈ S, o i = o i' → i = i' := by
    intro i hi i' hi' h
    rw [hS, Finset.mem_filter] at hi hi'
    obtain ⟨a, ha⟩ := (hr i).resolve_left hi.2
    obtain ⟨b, hb⟩ := (hr i').resolve_left hi'.2
    have h' : (p : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) := by
      refine ⟨a - b, ?_⟩
      have := h
      simp only [o, ha, hb] at this
      linarith
    have hi1 := i.2
    have hi2 := i'.2
    apply Fin.ext
    rcases h' with ⟨c, hc⟩
    have : c = 0 := by
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · exact hc0
      · nlinarith
    subst this
    omega
  obtain ⟨i₀, hi₀S, hmin⟩ := Finset.exists_min_image S o hSne

  have hcoeff : (∑ i, r i * J ^ (i : ℕ)).coeff (o i₀) = (r i₀ * J ^ (i₀ : ℕ)).coeff (o i₀) := by
    rw [HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single i₀]
    · intro i _ hii
      by_cases hiS : i ∈ S
      · apply HahnSeries.coeff_eq_zero_of_lt_order
        rw [horder i hiS]
        exact lt_of_le_of_ne (hmin i hiS) (fun h => hii (hdist i hiS i₀ hi₀S h.symm))
      · have : r i = 0 := by
          by_contra h; exact hiS (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
        rw [this, zero_mul, HahnSeries.coeff_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  have hr0 : r i₀ ≠ 0 := by
    have := hi₀S; rw [hS, Finset.mem_filter] at this; exact this.2
  have hne0 : (r i₀ * J ^ (i₀ : ℕ)).coeff (o i₀) ≠ 0 := by
    rw [← horder i₀ hi₀S]
    exact fun h => (mul_ne_zero hr0 (pow_ne_zero _ hJ0)) (HahnSeries.coeff_order_eq_zero.mp h)
  rw [hsum, HahnSeries.coeff_zero] at hcoeff
  exact hne0 hcoeff.symm

end Gamma3aOrd
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3 P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.AlgVert"

namespace Gamma3aPres

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel"

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
variable (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
  (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
    ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))

include hW₀ in

theorem exists_common_presentation {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (hg : ∀ i, g i ∈ W₀) :
    ∃ (b' : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) (b : ι → PowerSeries ↥(GaloisRep.ratLocalizedAt p)), b'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      ∀ i, (g i : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b') = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype (b i)) := by
  classical
  have h := fun i => (hW₀ (g i)).mp (hg i)
  choose a a' ha' h using h
  refine ⟨∏ i, a' i, fun i => a i * ∏ k ∈ Finset.univ.erase i, a' k, ?_, fun i => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha' i
  · rw [← Finset.mul_prod_erase Finset.univ a' (Finset.mem_univ i), map_mul, map_mul, ← mul_assoc, h i, map_mul, map_mul]

include hW₀ in

theorem map_eq_zero_of_mem_nonunits (T : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (hT : T ∈ W₀.nonunits) (N d : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) (hd : d.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0)
    (hpres : (T : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype d) = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype N)) : N.map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
  by_contra hN
  rcases (ValuationSubring.mem_nonunits_iff_or _).mp hT with h0 | hinv
  · rw [h0, ZeroMemClass.coe_zero, zero_mul] at hpres
    have : PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype N = 0 :=
      HahnSeries.ofPowerSeries_injective (hpres.symm.trans (map_zero _).symm)
    exact hN (by rw [PowerSeries.map_injective _ Subtype.val_injective (this.trans (map_zero _).symm), map_zero])
  · apply hinv
    rw [hW₀]
    refine ⟨d, N, hN, ?_⟩
    have hT0 : ((T : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) ≠ 0 := by
      intro h; apply hN
      rw [h, zero_mul] at hpres
      have : PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype N = 0 :=
        HahnSeries.ofPowerSeries_injective (hpres.symm.trans (map_zero _).symm)
      rw [PowerSeries.map_injective _ Subtype.val_injective (this.trans (map_zero _).symm), map_zero]
    push_cast
    rw [← hpres, ← mul_assoc, inv_mul_cancel₀ hT0, one_mul]

include hW₀ in

theorem mem_nonunits_of_map_eq_zero
    (hW₀₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.nonunits)
    (g : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (b b' : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) (hb' : b'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0)
    (hpres : (g : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b') = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b)) (hb : b.map (GaloisRep.ratLocalizedAtResidue p) = 0) : g ∈ W₀.nonunits := by

  have hdiv : ∀ i, ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∣ PowerSeries.coeff i b := fun i =>
    (Gamma3.res_eq_zero_iff p _).mp (by have := congrArg (PowerSeries.coeff i) hb; rwa [PowerSeries.coeff_map, map_zero] at this)
  choose t ht using hdiv
  have hbb : b = PowerSeries.C ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * PowerSeries.mk t := by
    ext i; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ht i]

  have hP0 : (p : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) p]
    exact fun h => (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0) (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))
  have hPF : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = (p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := map_natCast _ p
  have hb'0 : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b') ≠ 0 := by
    intro h0; apply hb'
    have h1 : PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b' = 0 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    rw [PowerSeries.map_injective _ Subtype.val_injective (h1.trans (map_zero _).symm), map_zero]
  set w : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := g * ((p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))⁻¹ with hw
  have hwW : w ∈ W₀ := by
    rw [hW₀]
    refine ⟨PowerSeries.mk t, b', hb', ?_⟩
    rw [hw]; push_cast
    rw [mul_right_comm, hpres, hbb, map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C, map_natCast, map_natCast,
      mul_comm (p : LaurentSeries ℚ), mul_assoc, mul_inv_cancel₀ hP0, mul_one]
  have hp0F : (p : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hg : g = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) * w := by rw [hPF, hw, mul_comm, inv_mul_cancel_right₀ hp0F]
  rw [hg, ValuationSubring.mem_nonunits_iff, map_mul]
  have h1 := (ValuationSubring.mem_nonunits_iff _).mp (hW₀₁' _ (Ideal.mem_span_singleton_self _))
  have h2 := (W₀.valuation_le_one_iff _).mpr hwW
  calc W₀.valuation (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) * W₀.valuation w
      ≤ W₀.valuation (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact h1

end Gamma3aPres
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3 P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.AlgVert"

namespace Gamma3aW0

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve _root_.ModularCurve.XHDRLevel _root_.P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel in

theorem isDVR_and_eq_of_le (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.nonunits)
    (hW₀₆ : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ W₀.nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀) :
    IsDiscreteValuationRing ↥W₀ ∧ ∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), W₀ ≤ V → V ≠ ⊤ → V = W₀ := by
  classical

  set P : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) with hPdef
  have hP0 : P ≠ 0 := by
    rw [hPdef, map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hPmem : P ∈ W₀ := hW₀₁ _
  have hPnu : P ∈ W₀.nonunits := hW₀₁' _ (Ideal.mem_span_singleton_self _)
  have hPinv : P⁻¹ ∉ W₀ := by
    rcases (ValuationSubring.mem_nonunits_iff_or W₀).mp hPnu with h | h
    · exact absurd h hP0
    · exact h
  let ϖ : ↥W₀ := ⟨P, hPmem⟩
  have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal ↥W₀ := (ValuationSubring.coe_mem_nonunits_iff (A := W₀)).mp hPnu
  have hϖnu : ¬ IsUnit ϖ := (IsLocalRing.mem_maximalIdeal _).mp hϖmax

  have hdiv : ∀ a : ↥W₀, ¬ IsUnit a → (a : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) * P⁻¹ ∈ W₀ := fun a ha =>
    hW₀₆ a ((ValuationSubring.coe_mem_nonunits_iff (A := W₀)).mpr ((IsLocalRing.mem_maximalIdeal _).mpr ha))

  have hirr : Irreducible ϖ := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    apply hPinv
    have e : P⁻¹ = ((a : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) * P⁻¹) * ((b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) * P⁻¹) := by
      have hab' : P = (a : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) * b := congrArg Subtype.val hab
      field_simp
      rw [hab']
    rw [e]
    exact mul_mem (hdiv a ha) (hdiv b hb)

  have hfac : ∀ {x : ↥W₀}, x ≠ 0 → ∃ n : ℕ, Associated (ϖ ^ n) x := by
    intro x hx
    have hx' : (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨n, u, hu, hu', hxe⟩ := Gamma3.exists_eq_pow_mul_unit_of_gaussPin p M H W₀ hW₀ (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) hx'
    have hu0 : u ≠ 0 := by rintro rfl; exact hx' (by rw [hxe, mul_zero])

    have hn : 0 ≤ n := by
      by_contra hneg
      simp only [not_le] at hneg
      apply hPinv

      have hPn : P ^ n ∈ W₀ := by
        have : P ^ n = (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) * u⁻¹ := by rw [hxe, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
        rw [this]; exact mul_mem x.2 hu'
      have e : P⁻¹ = P ^ n * P ^ ((-n - 1).toNat) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hP0]
        have : n + (-n - 1) = -1 := by ring
        rw [this, zpow_neg_one]
      rw [e]
      exact mul_mem hPn (pow_mem hPmem _)
    refine ⟨n.toNat, ?_⟩

    let uW : (↥W₀)ˣ := ⟨⟨u, hu⟩, ⟨u⁻¹, hu'⟩, Subtype.ext (mul_inv_cancel₀ hu0), Subtype.ext (inv_mul_cancel₀ hu0)⟩
    refine ⟨uW, Subtype.ext ?_⟩
    show (((ϖ ^ n.toNat : ↥W₀) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) * u = x
    rw [SubmonoidClass.coe_pow]
    change P ^ n.toNat * u = (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    rw [hxe, ← zpow_natCast, Int.toNat_of_nonneg hn]
  have hDVR : IsDiscreteValuationRing ↥W₀ :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, hfac⟩
  refine ⟨hDVR, fun V hle hV => ?_⟩
  haveI := hDVR
  exact (ValuationSubring.eq_of_le_of_ne_top W₀ hle hV).symm

end Gamma3aW0
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel.Gamma3 P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.AlgVert"

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.ModularCurve.XHDRLevel"
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (hEF : qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
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
    (hne : (W₀.comap σ.toAlgHom.toRingHom) ≠ W₀) :
    let ι : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (IntermediateField.inclusion hEF : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    letI : Algebra ↥(W₀.comap ι) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (ι.comp (W₀.comap ι).subtype).toAlgebra
    ∃ 𝔓₀ 𝔓₁ : Ideal ↥(integralClosure ↥(W₀.comap ι) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
      𝔓₀.IsPrime ∧ 𝔓₁.IsPrime ∧ 𝔓₀ ≠ ⊥ ∧ 𝔓₁ ≠ ⊥ ∧ 𝔓₀ ≠ 𝔓₁ ∧
      𝔓₀.LiesOver (IsLocalRing.maximalIdeal ↥(W₀.comap ι)) ∧ 𝔓₁.LiesOver (IsLocalRing.maximalIdeal ↥(W₀.comap ι)) ∧
      1 ≤ (IsLocalRing.maximalIdeal ↥(W₀.comap ι)).inertiaDeg' 𝔓₀ ∧
      p ≤ (IsLocalRing.maximalIdeal ↥(W₀.comap ι)).inertiaDeg' 𝔓₁ := by
  classical
  haveI hpr : Fact p.Prime := inferInstance
  have hp : p.Prime := Fact.out

  have hAB : qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤
      qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) := hEF

  have huniq := ModularCurve.XHDRLevel.valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd p M H hpM hpM2 hHp hj
  have hdeg := ModularCurve.XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one p M H hpM hpM2 hHp
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

  have hOV₀ : ∀ x : ↥V', algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) x ∈ W₀ := (hdom W₀ hW₀b).2.1
  have hOV₁ : ∀ x : ↥V', algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) x ∈ W₁ := (hdom W₁ hW₁b).2.1
  have hdm₀ := (hdom W₀ hW₀b).2.2
  have hdm₁ := (hdom W₁ hW₁b).2.2
  refine ⟨AlgVert.centre W₀ hOV₀, AlgVert.centre W₁ hOV₁, inferInstance, inferInstance,
    AlgVert.centre_ne_bot W₀ hOV₀ hdm₀, AlgVert.centre_ne_bot W₁ hOV₁ hdm₁, ?_,
    AlgVert.liesOver_centre W₀ hOV₀ hdm₀, AlgVert.liesOver_centre W₁ hOV₁ hdm₁, ?_, ?_⟩
  ·
    intro h
    apply hne
    symm
    rw [← AlgVert.eq_valuationSubringAtPrime W₀ hOV₀ (hdom W₀ hW₀b).1 (AlgVert.centre_ne_bot W₀ hOV₀ hdm₀),
      ← AlgVert.eq_valuationSubringAtPrime W₁ hOV₁ (hdom W₁ hW₁b).1 (AlgVert.centre_ne_bot W₁ hOV₁ hdm₁)]
    congr 1
    exact IsDedekindDomain.HeightOneSpectrum.ext h
  ·
    haveI := AlgVert.liesOver_centre W₀ hOV₀ hdm₀
    exact Ideal.inertiaDeg'_pos (IsLocalRing.maximalIdeal ↥V') (AlgVert.centre W₀ hOV₀)
  ·
    have hW₁top := (hdom W₁ hW₁b).1
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hp0 : p ≠ 0 := hp.ne_zero
    set jH : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := jAt (CohCarrier.GammaH M H) hj with hjH
    have hjW₀ : jH ∈ W₀ := by
      have := (hW₀₂ Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
      rwa [Polynomial.aeval_X] at this
    let y : Fin p → ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := fun i => σ.symm (jH ^ (i : ℕ))
    have hσW₁ : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ W₁ ↔ σ x ∈ W₀ := fun x => ValuationSubring.mem_comap
    have hy : ∀ i, y i ∈ W₁ := fun i => by
      rw [hσW₁]
      show σ (σ.symm (jH ^ (i : ℕ))) ∈ W₀
      rw [AlgEquiv.apply_symm_apply]
      exact pow_mem hjW₀ _
    suffices hres : ∀ c : Fin p → ↥V', (∑ i, algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (c i) * y i) ∈ W₁.nonunits →
        ∀ i, c i ∈ IsLocalRing.maximalIdeal ↥V' by
      have key := AlgVert.card_le_inertiaDeg_of_mem W₁ hOV₁ hdm₁ hW₁top y hy hres
      rw [Fintype.card_fin] at key
      exact key
    intro c hc i₀

    have hσnu : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ W₁.nonunits → σ x ∈ W₀.nonunits := by
      intro x hx
      rw [ValuationSubring.mem_nonunits_iff_or] at hx ⊢
      rcases hx with h | h
      · left; rw [h, map_zero]
      · right; rw [← map_inv₀]; exact fun hm => h ((hσW₁ _).mpr hm)
    have halg : ∀ x : ↥V', algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) x = ι (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) := fun x => rfl
    have hT : σ (∑ i, algebraMap ↥V' ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (c i) * y i) = ∑ i, σ (ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) * jH ^ (i : ℕ) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, halg]
      show σ (ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) * σ (σ.symm (jH ^ (i : ℕ))) = _
      rw [AlgEquiv.apply_symm_apply]
    have hTnu : (∑ i, σ (ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) * jH ^ (i : ℕ)) ∈ W₀.nonunits := hT ▸ hσnu _ hc

    obtain ⟨b', b, hb', hpres⟩ := Gamma3aPres.exists_common_presentation p M H W₀ hW₀ (fun i => ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))))
      (fun i => ValuationSubring.mem_comap.mp (c i).2)

    have hσc : ∀ i, ((σ (ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p ((ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) := by
      intro i
      rw [hσ (ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) (Gamma3.coe_incl p M H hpM hHp _), Gamma3.coe_incl]

    set J : LaurentSeries ℚ := ((jH : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) with hJdef
    have hJ : J = HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
      rw [hJdef, hjH, coe_jAt]; rfl

    set jNumR : PowerSeries ↥(GaloisRep.ratLocalizedAt p) := jNum.map (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) with hjNumR
    have hjNumRQ : jNumR.map (GaloisRep.ratLocalizedAt p).subtype = jNum.map (Int.castRingHom ℚ) := by
      rw [hjNumR, ← RingHom.ext_int ((GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))) (Int.castRingHom ℚ)]
      exact (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) (GaloisRep.ratLocalizedAt p).subtype)) jNum).symm
    set N : PowerSeries ↥(GaloisRep.ratLocalizedAt p) := ∑ i : Fin p, PowerSeries.expand p (NeZero.ne p) (b i) * PowerSeries.X ^ (p - 1 - (i : ℕ)) * jNumR ^ (i : ℕ) with hN
    set d : PowerSeries ↥(GaloisRep.ratLocalizedAt p) := PowerSeries.expand p (NeZero.ne p) b' * PowerSeries.X ^ (p - 1) with hdd
    have hd : d.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
      rw [hdd, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand]
      refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
      intro h0; apply hb'
      ext n
      have := congrArg (PowerSeries.coeff (p * n)) h0
      rwa [PowerSeries.coeff_expand_mul, map_zero] at this

    have hs : ∀ i : Fin p, J ^ (i : ℕ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1) =
        HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) ^ (i : ℕ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1 - (i : ℕ)) := by
      intro i
      have hsplit : p - 1 = (i : ℕ) + (p - 1 - (i : ℕ)) := by have := i.2; omega
      conv_lhs => rw [hsplit, pow_add, hJ, mul_pow, HahnSeries.single_pow, HahnSeries.single_pow]
      have e : HahnSeries.single ((i : ℕ) • (-1 : ℤ)) ((1 : ℚ) ^ (i : ℕ)) * HahnSeries.single ((i : ℕ) • (1 : ℤ)) ((1 : ℚ) ^ (i : ℕ)) = 1 := by
        rw [HahnSeries.single_mul_single, one_pow, mul_one, ← HahnSeries.single_zero_one]
        congr 1; simp
      calc HahnSeries.single ((i : ℕ) • (-1 : ℤ)) ((1 : ℚ) ^ (i : ℕ)) * HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) ^ (i : ℕ) *
            (HahnSeries.single ((i : ℕ) • (1 : ℤ)) ((1 : ℚ) ^ (i : ℕ)) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1 - (i : ℕ)))
          = (HahnSeries.single ((i : ℕ) • (-1 : ℤ)) ((1 : ℚ) ^ (i : ℕ)) * HahnSeries.single ((i : ℕ) • (1 : ℤ)) ((1 : ℚ) ^ (i : ℕ))) *
            (HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) ^ (i : ℕ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1 - (i : ℕ))) := by ring
        _ = _ := by rw [e, one_mul]

    have hpresT : ((∑ i, σ (ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))) * jH ^ (i : ℕ) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) *
        HahnSeries.ofPowerSeries ℤ ℚ (d.map (GaloisRep.ratLocalizedAt p).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (N.map (GaloisRep.ratLocalizedAt p).subtype) := by
      rw [hdd, hN, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand, map_mul, map_pow, HahnSeries.ofPowerSeries_X,
        ← ModularCurve.qExpand_ofPowerSeries_eq_expand, map_sum, map_sum]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσc i]
      simp only [map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand, hjNumRQ, HahnSeries.ofPowerSeries_X]
      rw [← ModularCurve.qExpand_ofPowerSeries_eq_expand]
      have hci : qExpand ℚ p ((ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ) ) *
          qExpand ℚ p (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b')) =
          qExpand ℚ p (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype (b i))) := by
        rw [← map_mul, hpres i]
      rw [← hJdef]
      calc qExpand ℚ p ((ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ)) * J ^ (i : ℕ) *
            (qExpand ℚ p (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b')) *
              HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1))
          = (qExpand ℚ p ((ι (c i : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ)) *
              qExpand ℚ p (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype b'))) *
            (J ^ (i : ℕ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1)) := by ring
        _ = qExpand ℚ p (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype (b i))) *
            (HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) ^ (i : ℕ) * HahnSeries.single (1 : ℤ) (1 : ℚ) ^ (p - 1 - (i : ℕ))) := by
          rw [hci, hs i]
        _ = _ := by ring
    have hN0 := Gamma3aPres.map_eq_zero_of_mem_nonunits p M H W₀ hW₀ _ hTnu N d hd hpresT

    have hjNumRk : jNumR.map (GaloisRep.ratLocalizedAtResidue p) = jNum.map (Int.castRingHom (ZMod p)) := by
      rw [hjNumR, ← RingHom.ext_int ((GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p))) (Int.castRingHom (ZMod p))]
      exact (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom ↥(GaloisRep.ratLocalizedAt p)) (GaloisRep.ratLocalizedAtResidue p))) jNum).symm
    have hNk : ∑ i : Fin p, PowerSeries.expand p (NeZero.ne p) ((b i).map (GaloisRep.ratLocalizedAtResidue p)) *
        PowerSeries.X ^ (p - 1 - (i : ℕ)) * (jNum.map (Int.castRingHom (ZMod p))) ^ (i : ℕ) = 0 := by
      have h := hN0
      rw [hN, map_sum] at h
      simp only [map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand, hjNumRk] at h
      exact h

    set Jk : LaurentSeries (ZMod p) := jqModC (ZMod p) with hJk
    have hJk' : Jk = HahnSeries.single (-1 : ℤ) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ (ZMod p) (jNum.map (Int.castRingHom (ZMod p))) := rfl
    set r : Fin p → LaurentSeries (ZMod p) := fun i =>
      qExpand (ZMod p) p (HahnSeries.ofPowerSeries ℤ (ZMod p) ((b i).map (GaloisRep.ratLocalizedAtResidue p))) with hr_def
    have hsk : ∀ i : Fin p, HahnSeries.single (1 : ℤ) (1 : ZMod p) ^ (p - 1 - (i : ℕ)) *
        HahnSeries.ofPowerSeries ℤ (ZMod p) (jNum.map (Int.castRingHom (ZMod p))) ^ (i : ℕ) *
        HahnSeries.single (-((p : ℤ) - 1)) (1 : ZMod p) = Jk ^ (i : ℕ) := by
      intro i
      have hi := i.2
      rw [hJk', mul_pow, HahnSeries.single_pow, HahnSeries.single_pow, one_pow, one_pow]
      have e : HahnSeries.single ((p - 1 - (i : ℕ)) • (1 : ℤ)) (1 : ZMod p) * HahnSeries.single (-((p : ℤ) - 1)) (1 : ZMod p) =
          HahnSeries.single ((i : ℕ) • (-1 : ℤ)) (1 : ZMod p) := by
        have hi2 : (i : ℕ) < p := i.2
        rw [HahnSeries.single_mul_single, mul_one,
          show (p - 1 - (i : ℕ)) • (1 : ℤ) + -((p : ℤ) - 1) = (i : ℕ) • (-1 : ℤ) from by
            simp only [nsmul_eq_mul, mul_one, smul_neg]; omega]
      rw [mul_right_comm, e]
    have hsumk : ∑ i, r i * Jk ^ (i : ℕ) = 0 := by
      have h1 := congrArg (fun x => HahnSeries.ofPowerSeries ℤ (ZMod p) x * HahnSeries.single (-((p : ℤ) - 1)) (1 : ZMod p)) hNk
      simp only [map_zero, zero_mul, map_sum, map_mul, map_pow, HahnSeries.ofPowerSeries_X, Finset.sum_mul] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      show qExpand (ZMod p) p (HahnSeries.ofPowerSeries ℤ (ZMod p) ((b i).map (GaloisRep.ratLocalizedAtResidue p))) * Jk ^ (i : ℕ) = _
      rw [ModularCurve.qExpand_ofPowerSeries_eq_expand, ← hsk i]
      ring
    have hr : ∀ i, r i = 0 ∨ (p : ℤ) ∣ (r i).order := by
      intro i
      by_cases h : HahnSeries.ofPowerSeries ℤ (ZMod p) ((b i).map (GaloisRep.ratLocalizedAtResidue p)) = 0
      · left; rw [hr_def]; show qExpand (ZMod p) p _ = 0; rw [h, map_zero]
      · right; exact ⟨_, ModularCurve.order_qExpandC (ZMod p) p h⟩
    have hall := Gamma3aOrd.eq_zero_of_sum_mul_pow_eq_zero p Jk (ModularCurve.jqModC_ne_zero_def _) (ModularCurve.order_jqModC_def _) r hr hsumk

    have hbi : (b i₀).map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
      have h1 := hall i₀
      rw [hr_def] at h1
      have h2 : HahnSeries.ofPowerSeries ℤ (ZMod p) ((b i₀).map (GaloisRep.ratLocalizedAtResidue p)) = 0 :=
        ModularCurve.qExpand_injective p (h1.trans (map_zero _).symm)
      exact HahnSeries.ofPowerSeries_injective (h2.trans (map_zero _).symm)
    have hnuW₀ : ι (c i₀ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ W₀.nonunits :=
      Gamma3aPres.mem_nonunits_of_map_eq_zero p M H W₀ hW₀ hW₀₁ hW₀₁' _ (b i₀) b' hb' (hpres i₀) hbi
    have hcnu : ((c i₀ : ↥V') : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) ∈ V'.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_or] at hnuW₀ ⊢
      rcases hnuW₀ with h | h
      · left; exact (map_eq_zero_iff ι ι.injective).mp h
      · right; exact fun hm => h (by rw [← map_inv₀]; exact ValuationSubring.mem_comap.mp hm)
    exact ValuationSubring.coe_mem_nonunits_iff.mp hcnu

end S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH (solution)
