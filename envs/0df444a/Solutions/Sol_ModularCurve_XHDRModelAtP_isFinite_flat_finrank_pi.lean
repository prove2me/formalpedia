-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/14042795-06fa-5b63-b8ad-98258570b589

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
import Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isReduced_sections_quotient_of_isReduced_pullback
import Theorems.Thm_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
import Theorems.Thm_Module_free_of_isRegular_of_span_eq_maximalIdeal
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_and_locallyOfFinitePresentation_pi
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
import Theorems.Thm_ModularCurve_XHDRLevel_isIntegral_X
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict
import Theorems.Thm_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.ModularCurve ModularCurve.XHDRLevel"

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

open scoped TensorProduct

def NoMaxMin (T : Type*) [CommRing T] (q : ℕ) : Prop :=
  ∀ P ∈ (Ideal.span {(q : T)}).minimalPrimes, ¬ P.IsMaximal

def NoChain (T : Type*) [CommRing T] (q : ℕ) : Prop :=
  ∀ 𝔮 𝔭 m : Ideal T, 𝔮.IsPrime → 𝔭.IsPrime → m.IsPrime → (q : T) ∈ 𝔮 → 𝔮 < 𝔭 → ¬ 𝔭 < m

theorem noMaxMin_and_noChain_of_ringKrullDim_eq_one (T : Type*) [CommRing T] (q : ℕ) (hq : (q : T) = 0)
    (hloc : ∀ (m : Ideal T) [m.IsMaximal], ringKrullDim (Localization.AtPrime m) = 1) :
    NoMaxMin T q ∧ NoChain T q := by
  have hspan : Ideal.span {(q : T)} = ⊥ := by rw [hq, Ideal.span_singleton_eq_bot]
  constructor
  · intro P hP hPmax
    rw [hspan] at hP
    haveI := hP.1.1
    have h0 : P.height = 0 := Ideal.height_eq_zero_iff.mpr hP
    have h1 := @hloc P hPmax
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), h0] at h1
    exact absurd h1 (by simp)
  · intro 𝔮 𝔭 m h𝔮 h𝔭 hm _ h1 h2
    obtain ⟨m', hm', hmm'⟩ := Ideal.exists_le_maximal m hm.ne_top
    haveI := hm'.isPrime
    have h2' : 𝔭 < m' := lt_of_lt_of_le h2 hmm'
    have ha := Ideal.height_add_one_le_of_lt_of_isPrime h1
    have hb := Ideal.height_add_one_le_of_lt_of_isPrime h2'
    have hd := @hloc m' hm'
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m' (Localization.AtPrime m')] at hd
    have hd' : m'.height = 1 := by exact_mod_cast hd
    have h3 : 𝔮.height + 1 + 1 ≤ m'.height := (add_le_add ha le_rfl).trans hb
    rw [hd'] at h3
    have h4 : (1 : ℕ∞) + 1 ≤ 𝔮.height + 1 + 1 := by
      gcongr
      exact le_add_self
    have h5 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans h3
    exact absurd h5 (by decide)

theorem noMaxMin_of_surjective {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (hf : Function.Surjective f) (q : ℕ) (hker : RingHom.ker f ≤ Ideal.span {(q : T)}) (h : NoMaxMin T' q) :
    NoMaxMin T q := by
  intro P hP hPmax
  have h1 := Ideal.minimalPrimes_map_of_surjective hf (Ideal.span {(q : T)})
  rw [sup_eq_left.mpr hker, Ideal.map_span, Set.image_singleton, map_natCast] at h1
  have h2 : P.map f ∈ (Ideal.span {(q : T')}).minimalPrimes := h1 ▸ ⟨P, hP, rfl⟩
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective f hf hPmax with htop | hmax
  · exact h2.1.1.ne_top htop
  · exact h _ h2 hmax

theorem noChain_of_surjective {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (hf : Function.Surjective f) (q : ℕ) (hker : RingHom.ker f ≤ Ideal.span {(q : T)}) (h : NoChain T' q) :
    NoChain T q := by
  intro 𝔮 𝔭 m h𝔮 h𝔭 hm hq h1 h2
  have hk𝔮 : RingHom.ker f ≤ 𝔮 := hker.trans ((Ideal.span_singleton_le_iff_mem _).mpr hq)
  have hk𝔭 : RingHom.ker f ≤ 𝔭 := hk𝔮.trans h1.le
  have hkm : RingHom.ker f ≤ m := hk𝔭.trans h2.le
  have hinj : ∀ I J : Ideal T, RingHom.ker f ≤ I → RingHom.ker f ≤ J → I.map f = J.map f → I = J := by
    intro I J hI hJ hIJ
    have := congrArg (Ideal.comap f) hIJ
    rwa [Ideal.comap_map_of_surjective f hf, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at this
  refine h (𝔮.map f) (𝔭.map f) (m.map f) (Ideal.map_isPrime_of_surjective hf hk𝔮)
    (Ideal.map_isPrime_of_surjective hf hk𝔭) (Ideal.map_isPrime_of_surjective hf hkm) ?_ ?_ ?_
  · rw [← map_natCast f q]; exact Ideal.mem_map_of_mem f hq
  · exact lt_of_le_of_ne (Ideal.map_mono h1.le) fun he => h1.ne (hinj _ _ hk𝔮 hk𝔭 he)
  · exact lt_of_le_of_ne (Ideal.map_mono h2.le) fun he => h2.ne (hinj _ _ hk𝔭 hkm he)

theorem noMaxMin_noChain_of_surjective {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (hf : Function.Surjective f) (q : ℕ) (hker : RingHom.ker f ≤ Ideal.span {(q : T)})
    (h : NoMaxMin T' q ∧ NoChain T' q) : NoMaxMin T q ∧ NoChain T q :=
  ⟨noMaxMin_of_surjective f hf q hker h.1, noChain_of_surjective f hf q hker h.2⟩

theorem noMaxMin_noChain_of_tensor {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (q : ℕ)
    (h : NoMaxMin ((R ⧸ Ideal.span {(q : R)}) ⊗[R] A) q ∧ NoChain ((R ⧸ Ideal.span {(q : R)}) ⊗[R] A) q) :
    NoMaxMin A q ∧ NoChain A q := by
  set I : Ideal R := Ideal.span {(q : R)} with hI
  have hmap : I.map (algebraMap R A) = Ideal.span {(q : A)} := by
    rw [hI, Ideal.map_span, Set.image_singleton, map_natCast]
  let e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] (R ⧸ I) := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
  let c : A ⊗[R] (R ⧸ I) ≃ₐ[R] (R ⧸ I) ⊗[R] A := Algebra.TensorProduct.comm R A (R ⧸ I)
  let f : A →+* (R ⧸ I) ⊗[R] A :=
    c.toRingEquiv.toRingHom.comp (e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap R A))))
  have hf : Function.Surjective f :=
    c.toRingEquiv.surjective.comp (e.toRingEquiv.surjective.comp Ideal.Quotient.mk_surjective)
  have hker : RingHom.ker f ≤ Ideal.span {(q : A)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : e.toRingEquiv (Ideal.Quotient.mk _ x) = 0 := c.toRingEquiv.injective (by simpa [f] using hx)
    have h2 : Ideal.Quotient.mk (I.map (algebraMap R A)) x = 0 := e.toRingEquiv.injective (by simpa using h1)
    rw [← hmap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  exact noMaxMin_noChain_of_surjective f hf q hker h

end ModularCurve.XHDRModelAtP.FlatPiH

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

open IsLocalRing

theorem free_localizedModule_of_dim_two
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [IsDomain A₀] [IsDomain B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀]
    (hinj : Function.Injective (algebraMap A₀ B₀)) (q : ℕ)
    (hred : IsReduced (B₀ ⧸ Ideal.span {(q : B₀)}))
    (hnomax : ∀ P ∈ (Ideal.span {(q : B₀)}).minimalPrimes, ¬ P.IsMaximal)
    (hchain : ∀ 𝔮 𝔭' m : Ideal A₀, 𝔮.IsPrime → 𝔭'.IsPrime → m.IsPrime → (q : A₀) ∈ 𝔮 → 𝔮 < 𝔭' → ¬ 𝔭' < m)
    (𝔭 : Ideal A₀) [𝔭.IsPrime] [IsNoetherianRing (Localization.AtPrime 𝔭)]
    (hq𝔪 : (q : Localization.AtPrime 𝔭) ∈ maximalIdeal (Localization.AtPrime 𝔭))
    (hq0 : (q : Localization.AtPrime 𝔭) ≠ 0)
    [IsDomain (Localization.AtPrime 𝔭 ⧸ Ideal.span {(q : Localization.AtPrime 𝔭)})]
    [IsDiscreteValuationRing (Localization.AtPrime 𝔭 ⧸ Ideal.span {(q : Localization.AtPrime 𝔭)})] :
    Module.Free (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl B₀) := by
  classical
  set A := Localization.AtPrime 𝔭 with hA
  let B := Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)
  haveI : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective A₀ B₀).mpr hinj
  haveI : IsDomain B := inferInstance
  haveI : Module.Finite A B := inferInstance
  haveI : Algebra.IsIntegral A₀ B₀ := inferInstance

  obtain ⟨t, hspan, hAreg⟩ :=
    IsLocalRing.exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
      (q : A) hq𝔪 hq0
  have ht𝔪 : t ∈ maximalIdeal A := by
    rw [← hspan]; exact Ideal.subset_span (by simp)

  have hqB : algebraMap A B (q : A) = (q : B) := map_natCast _ q
  have hqB0 : (q : B) ≠ 0 := by
    intro h
    apply hq0
    have h1 : algebraMap A B (q : A) = 0 := by rw [hqB, h]
    exact (FaithfulSMul.algebraMap_injective A B) (by rw [h1, map_zero])
  have ha : IsSMulRegular B (algebraMap A B (q : A)) := by
    rw [hqB]; exact fun x y h => mul_left_cancel₀ hqB0 h

  have hmapq : (Ideal.span {(q : B₀)}).map (algebraMap B₀ B) = Ideal.span {algebraMap A B (q : A)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, hqB]
  have hredB : IsReduced (B ⧸ Ideal.span {algebraMap A B (q : A)}) := by
    rw [← hmapq]
    haveI := hred
    exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (B₀ ⧸ Ideal.span {(q : B₀)})
      (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)) _ hred

  have h𝔭max : 𝔭.IsMaximal := by
    have hprime : (Ideal.span {(q : A)}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    set 𝔮 : Ideal A₀ := (Ideal.span {(q : A)}).under A₀ with h𝔮
    have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under _ _
    have hq𝔮 : (q : A₀) ∈ 𝔮 := by
      rw [h𝔮, Ideal.under, Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
    have h𝔭eq : (maximalIdeal A).under A₀ = 𝔭 := IsLocalization.AtPrime.comap_maximalIdeal A 𝔭
    have h𝔮le : 𝔮 ≤ 𝔭 := by
      rw [← h𝔭eq]; exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hq𝔪)
    have h𝔮ne : 𝔮 ≠ 𝔭 := by
      intro he
      have h1 : Ideal.span {(q : A)} = maximalIdeal A := by
        rw [← IsLocalization.map_under 𝔭.primeCompl A (Ideal.span {(q : A)}), ← h𝔮, he]
        exact Localization.AtPrime.map_eq_maximalIdeal
      have hF : IsField (A ⧸ Ideal.span {(q : A)}) := by
        rw [h1]; exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
      exact IsDiscreteValuationRing.not_isField _ hF
    by_contra hnm
    obtain ⟨m, hm, h𝔭m⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top inferInstance)
    have hne : 𝔭 ≠ m := fun he => hnm (he ▸ hm)
    exact hchain 𝔮 𝔭 m h𝔮p inferInstance hm.isPrime hq𝔮 (lt_of_le_of_ne h𝔮le h𝔮ne) (lt_of_le_of_ne h𝔭m hne)

  have hb : ∀ P ∈ minimalPrimes (B ⧸ Ideal.span {algebraMap A B (q : A)}),
      Ideal.Quotient.mk (Ideal.span {algebraMap A B (q : A)}) (algebraMap A B t) ∉ P := by
    intro P hP htP

    set P' : Ideal B := P.comap (Ideal.Quotient.mk _) with hP'
    have hP'min : P' ∈ (Ideal.span {algebraMap A B (q : A)}).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hP, rfl⟩
    haveI hP'p : P'.IsPrime := hP'min.1.1
    have hqP' : algebraMap A B (q : A) ∈ P' := hP'min.1.2 (Ideal.subset_span rfl)
    have htP' : algebraMap A B t ∈ P' := htP

    have hPA : P'.comap (algebraMap A B) = maximalIdeal A := by
      refine ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
      rw [← hspan, Ideal.ofList, Ideal.span_le]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
      rcases hx with rfl | rfl
      · exact hqP'
      · exact htP'

    set P₀ : Ideal B₀ := P'.comap (algebraMap B₀ B) with hP₀
    haveI : P₀.IsPrime := Ideal.IsPrime.comap _
    have hP₀A : P₀.comap (algebraMap A₀ B₀) = 𝔭 := by
      rw [hP₀, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A₀ A B,
        ← Ideal.comap_comap, hPA]
      exact IsLocalization.AtPrime.comap_maximalIdeal A 𝔭
    have hP₀min : P₀ ∈ (Ideal.span {(q : B₀)}).minimalPrimes := by
      have h := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl) B (Ideal.span {(q : B₀)})
      rw [hmapq] at h
      have : P' ∈ Ideal.under B₀ ⁻¹' (Ideal.span {(q : B₀)}).minimalPrimes := h ▸ hP'min
      exact this
    have hP₀max : P₀.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P₀ (hP₀A ▸ h𝔭max)
    exact hnomax P₀ hP₀min hP₀max

  haveI : Nontrivial B := inferInstance
  have hreg : RingTheory.Sequence.IsRegular B [(q : A), t] :=
    RingTheory.Sequence.isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
      (q : A) t hq𝔪 ht𝔪 ha hredB hb
  have hfreeB : Module.Free A B :=
    Module.free_of_isRegular_of_span_eq_maximalIdeal [(q : A), t] hAreg hspan B hreg

  have hloc : IsLocalizedModule 𝔭.primeCompl (IsScalarTower.toAlgHom A₀ B₀ B).toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr inferInstance
  let e₀ : LocalizedModule 𝔭.primeCompl B₀ ≃ₗ[A₀] B :=
    IsLocalizedModule.iso 𝔭.primeCompl (IsScalarTower.toAlgHom A₀ B₀ B).toLinearMap
  let e : LocalizedModule 𝔭.primeCompl B₀ ≃ₗ[A] B := LinearEquiv.extendScalarsOfIsLocalization 𝔭.primeCompl A e₀
  exact Module.Free.of_equiv e.symm

end ModularCurve.XHDRModelAtP.FlatPiH

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

theorem ringKrullDim_stalk_le_of_smoothOfRelativeDimension {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine (hU.ringKrullDim_stalk_le x hxU).trans ?_
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ n
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  haveI : SmoothOfRelativeDimension n (Scheme.Opens.ι U ≫ f) := by
    have h : SmoothOfRelativeDimension (0 + n) (Scheme.Opens.ι U ≫ f) := inferInstance
    rwa [Nat.zero_add] at h
  exact SmoothOfRelativeDimension.topologicalKrullDim_le (Scheme.Opens.ι U ≫ f) n

theorem maximalIdeal_stalk_spec_eq_map {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R)) :
    letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk t) =
      t.asIdeal.map (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk t)) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk t) t.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R t
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal t.asIdeal _).symm

section Crux

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)

theorem isLocalRing_R : IsLocalRing (R p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out

include 𝔛 in

theorem toBase0_apply_eq_closedPoint_of_not_ringKrullDim_le_one (y : X p (ΓN p M H hpM) hj)
    (hdim : ¬ ringKrullDim ((X p (ΓN p M H hpM) hj).presheaf.stalk y) ≤ 1) :
    (toBase p (ΓN p M H hpM) hj).base y = @IsLocalRing.closedPoint (R p) _ (isLocalRing_R p) := by
  haveI := isLocalRing_R p
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hsm : SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj) := 𝔛.smooth0
  by_contra hne
  apply hdim
  have hbot : ((toBase p (ΓN p M H hpM) hj).base y).asIdeal = ⊥ := by
    by_contra hb
    apply hne
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hb inferInstance)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := by
    have := @smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ hsm
  exact (isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing ℚ (toBase p (ΓN p M H hpM) hj)).2 1
    (fun z => ringKrullDim_stalk_le_of_smoothOfRelativeDimension (pullback.snd (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) 1 z) y hbot

include 𝔛 in

theorem natCast_mem_maximalIdeal_and_isDiscreteValuationRing_stalk_quotient (y : X p (ΓN p M H hpM) hj)
    (hdim : ¬ ringKrullDim ((X p (ΓN p M H hpM) hj).presheaf.stalk y) ≤ 1) :
    (p : (X p (ΓN p M H hpM) hj).presheaf.stalk y) ∈ IsLocalRing.maximalIdeal _ ∧
    (p : (X p (ΓN p M H hpM) hj).presheaf.stalk y) ≠ 0 ∧
    ∃ _ : IsDomain ((X p (ΓN p M H hpM) hj).presheaf.stalk y ⧸
        Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk y)}),
      IsDiscreteValuationRing ((X p (ΓN p M H hpM) hj).presheaf.stalk y ⧸
        Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk y)}) := by
  haveI := isLocalRing_R p
  have hy := toBase0_apply_eq_closedPoint_of_not_ringKrullDim_le_one p M H hpM hj 𝔛 y hdim
  have hsm : SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj) := 𝔛.smooth0
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  set f : X p (ΓN p M H hpM) hj ⟶ Spec (CommRingCat.of (R p)) := toBase p (ΓN p M H hpM) hj with hf
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 _
  set s : Spec (CommRingCat.of (R p)) := IsLocalRing.closedPoint (R p) with hs

  obtain ⟨z, hz⟩ : y ∈ Set.range (f.fiberι s).base := by
    rw [Scheme.Hom.range_fiberι]; exact hy
  subst hz

  have hSm : Smooth (f.fiberToSpecResidueField s) := by
    delta Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber
    exact MorphismProperty.pullback_snd _ _ ‹Smooth f›
  have hSmd : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField s) := by
    have := @smoothOfRelativeDimension_isStableUnderBaseChange 1
    delta Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber
    exact MorphismProperty.pullback_snd _ _ hsm
  have hregD : IsRegularLocalRing ((f.fiber s).presheaf.stalk z) :=
    @Smooth.isRegularLocalRing_stalk _ _ _ (f.fiberToSpecResidueField s) hSm z
  have hdimD : ringKrullDim ((f.fiber s).presheaf.stalk z) ≤ 1 :=
    @ringKrullDim_stalk_le_of_smoothOfRelativeDimension _ _ _ (f.fiberToSpecResidueField s) 1 hSmd z

  have hregA : IsRegularLocalRing ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z)) :=
    Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing (R p) f _

  have hsurj : Function.Surjective ((f.fiberι s).stalkMap z).hom := (f.fiberι s).stalkMap_surjective z
  have hker : RingHom.ker ((f.fiberι s).stalkMap z).hom =
      Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))} := by
    rw [ker_fiberIota_stalkMap_eq_maximalIdeal_map f s z, maximalIdeal_stalk_spec_eq_map, Ideal.map_map]
    have hfx : (f.base ((f.fiberι s).base z)).asIdeal = Ideal.span {(p : R p)} := by
      rw [hy]
      exact GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out
    rw [hfx, Ideal.map_span, Set.image_singleton, map_natCast]

  let e : ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))}) ≃+*
        (f.fiber s).presheaf.stalk z :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI : IsDomain ((f.fiber s).presheaf.stalk z) := @IsRegularLocalRing.isDomain _ _ hregD
  haveI hdomQ : IsDomain ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))}) :=
    MulEquiv.isDomain _ e.toMulEquiv
  have hregQ : IsRegularLocalRing ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))}) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have hdimQ : ringKrullDim ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))}) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]; exact hdimD

  have hqmax : (p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z)) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have htop := Ideal.span_singleton_eq_top.mpr hu
    haveI := Ideal.Quotient.subsingleton_iff.mpr htop
    exact not_subsingleton ((f.fiber s).presheaf.stalk z) e.symm.toEquiv.subsingleton

  have hQnf : ¬ IsField ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))}) := by
    intro hF
    apply hdim
    have hmax := Ideal.Quotient.maximal_of_isField _ hF

    have heq := (IsLocalRing.eq_maximalIdeal hmax).symm
    rw [← hregA.spanFinrank_maximalIdeal, heq]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))
      (M := (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))
      (Set.finite_singleton (p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z)))
    rw [Set.ncard_singleton] at h1
    exact_mod_cast h1

  have hq0 : (p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z)) ≠ 0 := by
    intro h0
    apply hdim
    have hbot : Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))} = ⊥ := by
      rw [h0]; exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [← ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _))]
    exact hdimQ

  haveI := hregQ
  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))})).mp hregQ
  have hle : Module.finrank (IsLocalRing.ResidueField ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))})) (IsLocalRing.CotangentSpace ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))})) ≤ 1 := by
    have h : (Module.finrank (IsLocalRing.ResidueField ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))})) (IsLocalRing.CotangentSpace ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))})) : WithBot ℕ∞) ≤ 1 := by
      rw [hfin]; exact hdimQ
    exact_mod_cast h
  refine ⟨hqmax, hq0, hdomQ, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · exact absurd (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h0) hQnf
  · exact ((IsDiscreteValuationRing.TFAE ((X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk ((f.fiberι s).base z))}) hQnf).out 0 5).mpr h1

end Crux
end ModularCurve.XHDRModelAtP.FlatPiH

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "j_ne_zero adjoin_le_chartAlg chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf chartFinOpen chartInfOpen isAffineOpen_chartFinOpen isAffineOpen_chartInfOpen twoChartCover fibre isIntegrallyClosed_chartAlg"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section ChartIntersection

variable (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem ιFin_apply_eq_ιInf_apply_iff (a : ↥(XFin R F j)) (b : ↥(XInf R F j)) :
    (ιFin R F j).base a = (ιInf R F j).base b ↔ ∃ m : ↥(XMid R F j), (fFin R F j).base m = a ∧ (fInf R F j).base m = b := by
  have h := Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
    (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := a) (xj := b)
  have h' : (ιFin R F j).base a = (ιInf R F j).base b ↔
      ∃ (k : WalkingSpan) (fi : k ⟶ WalkingSpan.left) (fj : k ⟶ WalkingSpan.right)
        (x : ↥((span (fFin R F j) (fInf R F j)).obj k)),
        ((span (fFin R F j) (fInf R F j)).map fi).base x = a ∧ ((span (fFin R F j) (fInf R F j)).map fj).base x = b := h
  rw [h']
  constructor
  · rintro ⟨k, fi, fj, x, ha, hb⟩
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WidePushoutShape.Hom.init _ := Subsingleton.elim _ _
      obtain rfl : fj = WidePushoutShape.Hom.init _ := Subsingleton.elim _ _
      exact ⟨x, ha, hb⟩
    · change WidePushoutShape.Hom _ _ at fj; cases fj
    · change WidePushoutShape.Hom _ _ at fi; cases fi
  · rintro ⟨m, ha, hb⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, m, ha, hb⟩

theorem ιInf_apply_mem_range_ιFin_iff (b : ↥(XInf R F j)) :
    (ιInf R F j).base b ∈ Set.range (ιFin R F j).base ↔ b ∈ Set.range (fInf R F j).base := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, -, hm⟩ := (ιFin_apply_eq_ιInf_apply_iff R F j a b).mp ha
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fFin R F j).base m, (ιFin_apply_eq_ιInf_apply_iff R F j _ _).mpr ⟨m, rfl, rfl⟩⟩

theorem ιFin_apply_mem_range_ιInf_iff (a : ↥(XFin R F j)) :
    (ιFin R F j).base a ∈ Set.range (ιInf R F j).base ↔ a ∈ Set.range (fFin R F j).base := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨m, hm, -⟩ := (ιFin_apply_eq_ιInf_apply_iff R F j a b).mp hb.symm
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fInf R F j).base m, ((ιFin_apply_eq_ιInf_apply_iff R F j _ _).mpr ⟨m, rfl, rfl⟩).symm⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fInf :
    Set.range (fInf R F j).base = (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fFin :
    Set.range (fFin R F j).base = (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum ↥(chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen :
    ιInf R F j ⁻¹ᵁ chartFinOpen R F j = PrimeSpectrum.basicOpen (jInvChartInf R F j) ∧
    ιFin R F j ⁻¹ᵁ chartInfOpen R F j = PrimeSpectrum.basicOpen (jChartFin R F j) := by
  constructor
  · apply TopologicalSpace.Opens.ext
    ext b
    change (ιInf R F j).base b ∈ Set.range (ιFin R F j).base ↔ b ∈ (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum ↥(chartAlgInf R F j)))
    rw [ιInf_apply_mem_range_ιFin_iff, range_fInf]
    exact Iff.rfl
  · apply TopologicalSpace.Opens.ext
    ext a
    change (ιFin R F j).base a ∈ Set.range (ιInf R F j).base ↔ a ∈ (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum ↥(chartAlgFin R F j)))
    rw [ιFin_apply_mem_range_ιInf_iff, range_fFin]
    exact Iff.rfl

noncomputable def ΓChartFinIso (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartFinOpen R F j) :
    Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) ≅ CommRingCat.of ↥(chartAlgFin R F j) :=
  (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.mapIso (eqToIso (congrArg Opposite.op hV)) ≪≫
    (IsOpenImmersion.ΓIsoTop (ιFin R F j)).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))

noncomputable def ΓChartInfIso (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartInfOpen R F j) :
    Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) ≅ CommRingCat.of ↥(chartAlgInf R F j) :=
  (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.mapIso (eqToIso (congrArg Opposite.op hV)) ≪≫
    (IsOpenImmersion.ΓIsoTop (ιInf R F j)).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))

theorem isDomain_sections_of_eq_chartFinOpen (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartFinOpen R F j) :
    IsDomain Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) :=
  (ΓChartFinIso R F j V hV).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

theorem isDomain_sections_of_eq_chartInfOpen (V : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens) (hV : V = chartInfOpen R F j) :
    IsDomain Γ(AlgebraicCurve.TwoChartIntegralModel R F j, V) :=
  (ΓChartInfIso R F j V hV).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

end ChartIntersection

end AlgebraicCurve.TwoChartIntegralModel

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.ModularCurve ModularCurve.XHDRLevel"

section Pi

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

abbrev KΓ (Γ : Subgroup SL(2, ℤ)) : Type := ↥(qExpFunctionFieldC ℚ Γ)

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_jChartFin :
    𝔛.iota0 (jChartFin (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) = jChartFin (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔛.iota0_spec, coe_jChartFin, coe_jChartFin, coe_jAt, coe_jAt]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_jInvChartInf :
    𝔛.iotaInf (jInvChartInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) = jInvChartInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔛.iotaInf_spec, coe_jInvChartInf, coe_jInvChartInf, IntermediateField.coe_inv, IntermediateField.coe_inv, coe_jAt, coe_jAt]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_injective : Function.Injective 𝔛.iota0 := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  rw [← 𝔛.iota0_spec a, ← 𝔛.iota0_spec b, h]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_injective : Function.Injective 𝔛.iotaInf := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  rw [← 𝔛.iotaInf_spec a, ← 𝔛.iotaInf_spec b, h]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιFin :
    𝔛.π.1.base ⁻¹' Set.range (ιFin p (ΓN p M H hpM) hj).base = Set.range (ιFin p (ΓM M H) hj).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) x with h | ⟨y, rfl⟩
    · exact h
    · have e : 𝔛.π.1.base ((ιInf p (ΓM M H) hj).base y) =
          (ιInf p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔛.pi_chartInf, Scheme.Hom.comp_apply]
      have hx' : (ιInf p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y) ∈
          Set.range (ιFin p (ΓN p M H hpM) hj).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y ∈
          ιInf p (ΓN p M H hpM) hj ⁻¹ᵁ chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) := hx'
      rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)).1] at h0
      have h0' : jInvChartInf (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) ∉
          ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jInvChartInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) ∉ y.asIdeal := by
        rw [← iotaInf_jInvChartInf 𝔛]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιInf p (ΓM M H) hj ⁻¹ᵁ chartFinOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
        rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj)).1]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
  · rintro _ ⟨y, rfl⟩
    show 𝔛.π.1.base ((ιFin p (ΓM M H) hj).base y) ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base
    rw [← Scheme.Hom.comp_apply, 𝔛.pi_chart, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιInf :
    𝔛.π.1.base ⁻¹' Set.range (ιInf p (ΓN p M H hpM) hj).base = Set.range (ιInf p (ΓM M H) hj).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) x with ⟨y, rfl⟩ | h
    · have e : 𝔛.π.1.base ((ιFin p (ΓM M H) hj).base y) =
          (ιFin p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔛.pi_chart, Scheme.Hom.comp_apply]
      have hx' : (ιFin p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y) ∈
          Set.range (ιInf p (ΓN p M H hpM) hj).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y ∈
          ιFin p (ΓN p M H hpM) hj ⁻¹ᵁ chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) := hx'
      rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)).2] at h0
      have h0' : jChartFin (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) ∉
          ((Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jChartFin (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) ∉ y.asIdeal := by
        rw [← iota0_jChartFin 𝔛]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιFin p (ΓM M H) hj ⁻¹ᵁ chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) := by
        rw [(ιInf_preimage_chartFinOpen_and_ιFin_preimage_chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj)).2]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
    · exact h
  · rintro _ ⟨y, rfl⟩
    show 𝔛.π.1.base ((ιInf p (ΓM M H) hj).base y) ∈ Set.range (ιInf p (ΓN p M H hpM) hj).base
    rw [← Scheme.Hom.comp_apply, 𝔛.pi_chartInf, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem preimage_chartFinOpen :
    𝔛.π.1 ⁻¹ᵁ chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) = chartFinOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) :=
  TopologicalSpace.Opens.ext (preimage_range_ιFin 𝔛)

theorem preimage_chartInfOpen :
    𝔛.π.1 ⁻¹ᵁ chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) = chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) :=
  TopologicalSpace.Opens.ext (preimage_range_ιInf 𝔛)

theorem appLE_congrHom {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

theorem injective_appTop_specMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective ((Spec.map (CommRingCat.ofHom φ)).appTop).hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h' : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h']
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective.comp
    (hφ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective)

theorem bijective_appLE_opensRange_top {X Y : Scheme} (ι : X ⟶ Y) [IsOpenImmersion ι]
    (e : (⊤ : X.Opens) ≤ ι ⁻¹ᵁ ι.opensRange) : Function.Bijective (ι.appLE ι.opensRange ⊤ e).hom := by
  haveI : IsIso (ι.app ι.opensRange) := ι.isIso_app _ le_rfl
  have htop : ι ⁻¹ᵁ ι.opensRange = ⊤ := ι.preimage_opensRange
  have hid : (homOfLE e).op = (eqToHom htop.symm).op := Subsingleton.elim _ _
  have : IsIso (ι.appLE ι.opensRange ⊤ e) := by
    rw [Scheme.Hom.appLE, hid, eqToHom_op]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (ι.appLE ι.opensRange ⊤ e)

theorem injective_app_opensRange_of_sq {X Y U V : Scheme} (π : X ⟶ Y) (ι : U ⟶ Y) (ι' : V ⟶ X) (σ : V ⟶ U)
    [IsOpenImmersion ι] [IsOpenImmersion ι'] (hsq : ι' ≫ π = σ ≫ ι)
    (hσ : Function.Injective (σ.appTop).hom) : Function.Injective (π.app ι.opensRange).hom := by
  have e₃ : (⊤ : U.Opens) ≤ ι ⁻¹ᵁ ι.opensRange := fun x _ => ⟨x, rfl⟩
  have e₁ : (⊤ : V.Opens) ≤ ι' ⁻¹ᵁ (π ⁻¹ᵁ ι.opensRange) := by
    intro x _
    show π.base (ι'.base x) ∈ Set.range ι.base
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have e₄ : (⊤ : V.Opens) ≤ σ ⁻¹ᵁ ⊤ := le_top.trans (le_of_eq (TopologicalSpace.Opens.map_top _).symm)
  have h1 : π.app ι.opensRange ≫ ι'.appLE (π ⁻¹ᵁ ι.opensRange) ⊤ e₁ = (ι' ≫ π).appLE ι.opensRange ⊤ (by exact e₁) := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (ι' ≫ π).appLE ι.opensRange ⊤ (by exact e₁) = (σ ≫ ι).appLE ι.opensRange ⊤ (hsq ▸ (by exact e₁)) :=
    appLE_congrHom hsq _ _ _
  have h3 : ι.appLE ι.opensRange ⊤ e₃ ≫ σ.appLE ⊤ ⊤ e₄ = (σ ≫ ι).appLE ι.opensRange ⊤ (hsq ▸ (by exact e₁)) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h4 : σ.appLE ⊤ ⊤ e₄ = σ.appTop := by
    have hid : (homOfLE e₄).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, hid]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hcomp : π.app ι.opensRange ≫ ι'.appLE (π ⁻¹ᵁ ι.opensRange) ⊤ e₁ = ι.appLE ι.opensRange ⊤ e₃ ≫ σ.appTop := by
    rw [h1, h2, ← h3, h4]
  have hinj : Function.Injective (ι.appLE ι.opensRange ⊤ e₃ ≫ σ.appTop).hom := by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact hσ.comp (bijective_appLE_opensRange_top ι e₃).1
  rw [← hcomp] at hinj
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hinj
  exact Function.Injective.of_comp hinj

set_option synthInstance.maxHeartbeats 1600000 in

theorem injective_app_chartFinOpen : Function.Injective (𝔛.π.1.app (chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))).hom :=
  injective_app_opensRange_of_sq 𝔛.π.1 (ιFin p (ΓN p M H hpM) hj) (ιFin p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom))
    𝔛.pi_chart (injective_appTop_specMap 𝔛.iota0.toRingHom (iota0_injective 𝔛))

set_option synthInstance.maxHeartbeats 1600000 in

theorem injective_app_chartInfOpen : Function.Injective (𝔛.π.1.app (chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))).hom :=
  injective_app_opensRange_of_sq 𝔛.π.1 (ιInf p (ΓN p M H hpM) hj) (ιInf p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom))
    𝔛.pi_chartInf (injective_appTop_specMap 𝔛.iotaInf.toRingHom (iotaInf_injective 𝔛))

end Pi

end ModularCurve.XHDRModelAtP.FlatPiH

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "j_ne_zero adjoin_le_chartAlg chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf chartFinOpen chartInfOpen isAffineOpen_chartFinOpen isAffineOpen_chartInfOpen twoChartCover fibre isIntegrallyClosed_chartAlg"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"
open scoped TensorProduct

section FiniteTypeAndDim

variable (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem finiteType_chartAlgFin_and_chartAlgInf_of_locallyOfFinitePresentation [LocallyOfFinitePresentation (toBase R F j)] :
    Algebra.FiniteType R ↥(chartAlgFin R F j) ∧ Algebra.FiniteType R ↥(chartAlgInf R F j) := by
  constructor
  · have h1 : LocallyOfFinitePresentation (ιFin R F j ≫ toBase R F j) := inferInstance
    rw [ιFin_toBase] at h1
    have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp h1
    exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_finitePresentation h2)
  · have h1 : LocallyOfFinitePresentation (ιInf R F j ≫ toBase R F j) := inferInstance
    rw [ιInf_toBase] at h1
    have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp h1
    exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_finitePresentation h2)

variable {R F} in

noncomputable def adjoinEquivOfTranscendental {t : F} (ht : Transcendental R t) : R[X] ≃ₐ[R] ↥(Algebra.adjoin R ({t} : Set F)) :=
  (AlgEquiv.ofInjective (aeval t) ((transcendental_iff_injective).mp ht)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval R t).symm)

variable {j} in
omit [Fact (j ≠ 0)] in
theorem transcendental_inv_of_transcendental (hj0 : j ≠ 0) (ht : Transcendental R j) : Transcendental R j⁻¹ := by
  rintro ⟨q, hq0, hq⟩
  apply ht
  letI : Invertible j⁻¹ := invertibleOfNonzero (inv_ne_zero hj0)
  refine ⟨q.reverse, fun h => hq0 (Polynomial.reverse_eq_zero.mp h), ?_⟩
  have key := Polynomial.eval₂_reverse_mul_pow (algebraMap R F) j⁻¹ q
  rw [Polynomial.aeval_def] at hq
  have h2 : Polynomial.eval₂ (algebraMap R F) (⅟ j⁻¹) q.reverse = 0 := by
    rcases mul_eq_zero.mp (key.trans hq) with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ (inv_ne_zero hj0))
  rwa [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def] at h2

theorem ringKrullDim_localization_chartAlgFin_tensor_eq_one [IsDomain R] [IsPrincipalIdealRing R]
    [LocallyOfFinitePresentation (toBase R F j)] (ht : Transcendental R j)
    {ϖ : R} (hϖ : Irreducible ϖ) (k : Type) [Field k] [Algebra R k] (hk : algebraMap R k ϖ = 0)
    (m : Ideal (k ⊗[R] ↥(chartAlgFin R F j))) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 :=
  Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hϖ (Algebra.adjoin R ({j} : Set F)) (chartAlgFin R F j)
    (adjoinEquivOfTranscendental ht) (adjoin_le_chartAlg R F _) (fun a => a.2)
    (finiteType_chartAlgFin_and_chartAlgInf_of_locallyOfFinitePresentation R F j).1 (isIntegrallyClosed_chartAlg R F _) k hk m

theorem ringKrullDim_localization_chartAlgInf_tensor_eq_one [IsDomain R] [IsPrincipalIdealRing R]
    [LocallyOfFinitePresentation (toBase R F j)] (ht : Transcendental R j)
    {ϖ : R} (hϖ : Irreducible ϖ) (k : Type) [Field k] [Algebra R k] (hk : algebraMap R k ϖ = 0)
    (m : Ideal (k ⊗[R] ↥(chartAlgInf R F j))) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 :=
  Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hϖ (Algebra.adjoin R ({j⁻¹} : Set F)) (chartAlgInf R F j)
    (adjoinEquivOfTranscendental (transcendental_inv_of_transcendental R F (j_ne_zero j) ht)) (adjoin_le_chartAlg R F _) (fun a => a.2)
    (finiteType_chartAlgFin_and_chartAlgInf_of_locallyOfFinitePresentation R F j).2 (isIntegrallyClosed_chartAlg R F _) k hk m

end FiniteTypeAndDim

end AlgebraicCurve.TwoChartIntegralModel

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.ModularCurve ModularCurve.XHDRLevel IsLocalRing Polynomial AlgebraicGeometry.Polynomial"

open scoped TensorProduct MatrixGroups

theorem ker_toRingHom_le {T T' : Type*} [CommRing T] [CommRing T'] (e : T ≃+* T') (I : Ideal T) :
    RingHom.ker e.toRingHom ≤ I := by
  intro x hx
  have hx' : e x = 0 := hx
  rw [map_eq_zero_iff e e.injective] at hx'
  rw [hx']
  exact I.zero_mem

section ChartRings

set_option synthInstance.maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem isMaximal_span_natCast_R : (Ideal.span {(p : R p)}).IsMaximal := by
  haveI : IsLocalRing (R p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out
  rw [← GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out]
  exact IsLocalRing.maximalIdeal.isMaximal _

theorem algebraMap_ratLocalizedAt_injective : Function.Injective (algebraMap (R p) ℚ) := Subtype.val_injective

theorem transcendental_jAt : Transcendental (R p) (jAt Γ hj) := by
  rintro ⟨f, hf0, hf⟩
  apply ModularCurve.transcendental_jq
  refine ⟨f.map (algebraMap (R p) ℚ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap_ratLocalizedAt_injective p)).mpr hf0
  · have h := congrArg (algebraMap (KΓ Γ) (LaurentSeries ℚ)) hf
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap ℚ (LaurentSeries ℚ)).comp (algebraMap (R p) ℚ) =
        (algebraMap (KΓ Γ) (LaurentSeries ℚ)).comp (algebraMap (R p) (KΓ Γ)) := by
      refine RingHom.ext fun a => ?_
      change algebraMap ℚ (LaurentSeries ℚ) (a : ℚ) =
        ((algebraMap ℚ (KΓ Γ) (a : ℚ) : KΓ Γ) : LaurentSeries ℚ)
      first
        | rfl
        | exact (IntermediateField.algebraMap_apply _ _).symm
        | simp
    rw [hcomp]
    exact h

theorem noMaxMin_noChain_chartAlgFin [LocallyOfFinitePresentation (toBase p Γ hj)] :
    NoMaxMin ↥(chartAlgFin p Γ hj) p ∧ NoChain ↥(chartAlgFin p Γ hj) p := by
  haveI hmax := isMaximal_span_natCast_R p
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  letI : Field (R p ⧸ Ideal.span {(p : R p)}) := Ideal.Quotient.field _
  haveI : CharP (R p ⧸ Ideal.span {(p : R p)}) p :=
    CharP.quotient (R p) p (mem_nonunits_iff.mpr fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  refine noMaxMin_noChain_of_tensor (R := R p) (A := ↥(chartAlgFin p Γ hj)) p
    (noMaxMin_and_noChain_of_ringKrullDim_eq_one _ p ?_ ?_)
  · have h0 : ((p : ℕ) : R p ⧸ Ideal.span {(p : R p)}) = 0 := CharP.cast_eq_zero _ p
    rw [← map_natCast (algebraMap (R p ⧸ Ideal.span {(p : R p)})
      ((R p ⧸ Ideal.span {(p : R p)}) ⊗[R p] ↥(chartAlgFin p Γ hj))) p, h0, map_zero]
  · intro m hm
    have h0 : algebraMap (R p) (R p ⧸ Ideal.span {(p : R p)}) (p : R p) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self _
    exact ringKrullDim_localization_chartAlgFin_tensor_eq_one (R p) (KΓ Γ) (jAt Γ hj) (transcendental_jAt p Γ hj)
      (GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out) (R p ⧸ Ideal.span {(p : R p)}) h0 m

theorem noMaxMin_noChain_chartAlgInf [LocallyOfFinitePresentation (toBase p Γ hj)] :
    NoMaxMin ↥(chartAlgInf p Γ hj) p ∧ NoChain ↥(chartAlgInf p Γ hj) p := by
  haveI hmax := isMaximal_span_natCast_R p
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  letI : Field (R p ⧸ Ideal.span {(p : R p)}) := Ideal.Quotient.field _
  haveI : CharP (R p ⧸ Ideal.span {(p : R p)}) p :=
    CharP.quotient (R p) p (mem_nonunits_iff.mpr fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  refine noMaxMin_noChain_of_tensor (R := R p) (A := ↥(chartAlgInf p Γ hj)) p
    (noMaxMin_and_noChain_of_ringKrullDim_eq_one _ p ?_ ?_)
  · have h0 : ((p : ℕ) : R p ⧸ Ideal.span {(p : R p)}) = 0 := CharP.cast_eq_zero _ p
    rw [← map_natCast (algebraMap (R p ⧸ Ideal.span {(p : R p)})
      ((R p ⧸ Ideal.span {(p : R p)}) ⊗[R p] ↥(chartAlgInf p Γ hj))) p, h0, map_zero]
  · intro m hm
    have h0 : algebraMap (R p) (R p ⧸ Ideal.span {(p : R p)}) (p : R p) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self _
    exact ringKrullDim_localization_chartAlgInf_tensor_eq_one (R p) (KΓ Γ) (jAt Γ hj) (transcendental_jAt p Γ hj)
      (GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out) (R p ⧸ Ideal.span {(p : R p)}) h0 m

theorem noMaxMin_noChain_sections_of_eq_chartFinOpen [LocallyOfFinitePresentation (toBase p Γ hj)] (V : (X p Γ hj).Opens)
    (hV : V = chartFinOpen (R p) (KΓ Γ) (jAt Γ hj)) :
    NoMaxMin Γ(X p Γ hj, V) p ∧ NoChain Γ(X p Γ hj, V) p :=
  let e := (ΓChartFinIso (R p) (KΓ Γ) (jAt Γ hj) V hV).commRingCatIsoToRingEquiv
  noMaxMin_noChain_of_surjective e.toRingHom e.surjective p
    (ker_toRingHom_le e _) (noMaxMin_noChain_chartAlgFin p Γ hj)

theorem noMaxMin_noChain_sections_of_eq_chartInfOpen [LocallyOfFinitePresentation (toBase p Γ hj)] (V : (X p Γ hj).Opens)
    (hV : V = chartInfOpen (R p) (KΓ Γ) (jAt Γ hj)) :
    NoMaxMin Γ(X p Γ hj, V) p ∧ NoChain Γ(X p Γ hj, V) p :=
  let e := (ΓChartInfIso (R p) (KΓ Γ) (jAt Γ hj) V hV).commRingCatIsoToRingEquiv
  noMaxMin_noChain_of_surjective e.toRingHom e.surjective p
    (ker_toRingHom_le e _) (noMaxMin_noChain_chartAlgInf p Γ hj)

end ChartRings

end ModularCurve.XHDRModelAtP.FlatPiH

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.ModularCurve ModularCurve.XHDRLevel IsLocalRing"

open scoped TensorProduct MatrixGroups

theorem exists_place (p : ℕ) [Fact p.Prime] :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (ρ : R p →+* ↥A),
      A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ) := by
  haveI : IsLocalRing (R p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out

  set f : R p →+* AlgebraicClosure ℚ := algebraMap (R p) (AlgebraicClosure ℚ) with hf
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have hrange : (LocalSubring.range f).toSubring = f.range := LocalSubring.range_toSubring f

  have hmem : ∀ a : R p, f a ∈ V.toSubring := fun a => hle (by rw [hrange]; exact ⟨a, rfl⟩)
  let ρ : R p →+* ↥V :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨V, ?_, ρ, RingHom.ext fun a => rfl⟩

  have hpR : ¬ IsUnit ((p : ℕ) : R p) := by
    have hirr := GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out
    exact hirr.not_isUnit
  have hpV : ¬ IsUnit (ρ (p : R p)) := by
    intro hu

    let x : ↥((LocalSubring.range f).toSubring) := ⟨f (p : R p), by rw [hrange]; exact ⟨_, rfl⟩⟩
    have hx : Subring.inclusion hle x = ρ (p : R p) := rfl
    have hux : IsUnit x := by
      haveI := hloc
      exact (isUnit_map_iff (Subring.inclusion hle) x).mp (hx ▸ hu)

    apply hpR
    obtain ⟨y, hy⟩ := hux.exists_left_inv
    have hy1 : (y : AlgebraicClosure ℚ) * f (p : R p) = 1 := by
      have := congrArg (fun z : ↥((LocalSubring.range f).toSubring) => (z : AlgebraicClosure ℚ)) hy
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      first | simpa [map_natCast] using this | (simp [map_natCast] at this; exact this) | exact this
    have hymem : (y : AlgebraicClosure ℚ) ∈ f.range := by rw [← hrange]; exact y.2
    obtain ⟨b, hb⟩ := hymem
    have hfinj : Function.Injective f := by
      rw [hf, IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)]
      exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective
    have hbp : b * (p : R p) = 1 := hfinj (by rw [map_mul, map_one, hb, hy1])
    exact IsUnit.of_mul_eq_one b (by rw [mul_comm]; exact hbp)
  exact (V.mem_nonunits_iff).2 ((V.valuation_lt_one_iff (ρ (p : R p))).1
    ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (by simpa [map_natCast] using hpV))))

theorem natCast_mem_maximalIdeal_of_liesOverPrime (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [A.valuation_lt_one_iff]
  simpa using (A.mem_nonunits_iff).1 hA

theorem charP_residueField_of_liesOverPrime (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) : CharP (IsLocalRing.ResidueField ↥A) p := by
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField ↥A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]
    exact natCast_mem_maximalIdeal_of_liesOverPrime p A hA
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 h0

section PerPoint

set_option synthInstance.maxHeartbeats 1600000

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
variable (U : (X p (ΓN p M H hpM) hj).Opens) (hU : IsAffineOpen U) (y : X p (ΓN p M H hpM) hj) (hy : y ∈ U)

@[reducible] noncomputable def algB₀ : Algebra Γ(X p (ΓN p M H hpM) hj, U) Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U) :=
  (𝔛.π.1.app U).hom.toAlgebra

noncomputable abbrev 𝔭 : Ideal Γ(X p (ΓN p M H hpM) hj, U) := (hU.primeIdealOf ⟨y, hy⟩).asIdeal

theorem L1_free_of_dim_le_one {A : Type*} [CommRing A] [IsRegularLocalRing A] [IsDomain A] (hdim : ringKrullDim A ≤ 1)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] : Module.Free A M := by
  haveI : IsPrincipalIdealRing A := by
    by_cases hF : IsField A
    · letI := hF.toField
      infer_instance
    · have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
      have hle : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) ≤ 1 := by
        have h : (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : WithBot ℕ∞) ≤ 1 := by
          rw [hreg]; exact hdim
        exact_mod_cast h
      have h1 : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · exact absurd (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h0) hF
        · exact h1
      haveI : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hF).out 0 5).mpr h1
      infer_instance
  exact Module.free_of_finite_type_torsion_free'

include 𝔛 in

theorem isRegularLocalRing_A : IsRegularLocalRing (Localization.AtPrime (𝔭 U hU y hy)) := by
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj) := 𝔛.smooth0
  haveI : Smooth (toBase p (ΓN p M H hpM) hj) := SmoothOfRelativeDimension.smooth 1 _
  letI := (X p (ΓN p M H hpM) hj).presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  haveI : IsRegularLocalRing ((X p (ΓN p M H hpM) hj).presheaf.stalk y) :=
    Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing (R p) (toBase p (ΓN p M H hpM) hj) y
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (𝔭 U hU y hy).primeCompl ((X p (ΓN p M H hpM) hj).presheaf.stalk y)
      (Localization.AtPrime (𝔭 U hU y hy))).toRingEquiv

include hU in

theorem finite_B₀ [IsFinite 𝔛.π.1] :
    letI := algB₀ 𝔛 U
    Module.Finite Γ(X p (ΓN p M H hpM) hj, U) Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U) := by
  letI := algB₀ 𝔛 U
  exact (RingHom.finite_algebraMap).mp (by
    simpa [algB₀, RingHom.algebraMap_toAlgebra] using IsFinite.finite_app 𝔛.π.1 U hU)

theorem isTorsionFree_M (hdomA : IsDomain Γ(X p (ΓN p M H hpM) hj, U)) (hdomB : IsDomain Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U))
    (hinj : Function.Injective (𝔛.π.1.app U).hom) :
    letI := algB₀ 𝔛 U
    Module.IsTorsionFree (Localization.AtPrime (𝔭 U hU y hy))
      (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U)) := by
  letI := algB₀ 𝔛 U
  haveI := hdomA
  haveI := hdomB
  haveI : Module.IsTorsionFree Γ(X p (ΓN p M H hpM) hj, U) Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  infer_instance

theorem free_M_of_not_dim_le_one [IsFinite 𝔛.π.1]
    (hdomA : IsDomain Γ(X p (ΓN p M H hpM) hj, U)) (hdomB : IsDomain Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U))
    (hinj : Function.Injective (𝔛.π.1.app U).hom)
    (hnomax : NoMaxMin Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U) p) (hchain : NoChain Γ(X p (ΓN p M H hpM) hj, U) p)
    (hdim : ¬ ringKrullDim (Localization.AtPrime (𝔭 U hU y hy)) ≤ 1) :
    letI := algB₀ 𝔛 U
    Module.Free (Localization.AtPrime (𝔭 U hU y hy))
      (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U)) := by
  classical
  letI := algB₀ 𝔛 U
  haveI := hdomA
  haveI := hdomB
  haveI := finite_B₀ 𝔛 U hU
  haveI := isRegularLocalRing_A 𝔛 U hU y hy

  letI := (X p (ΓN p M H hpM) hj).presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  set A := Localization.AtPrime (𝔭 U hU y hy) with hAdef
  let e : A ≃+* (X p (ΓN p M H hpM) hj).presheaf.stalk y :=
    (IsLocalization.algEquiv (𝔭 U hU y hy).primeCompl A ((X p (ΓN p M H hpM) hj).presheaf.stalk y)).toRingEquiv
  have heq : e (p : A) = (p : (X p (ΓN p M H hpM) hj).presheaf.stalk y) := map_natCast e p

  have hdimS : ¬ ringKrullDim ((X p (ΓN p M H hpM) hj).presheaf.stalk y) ≤ 1 := by rwa [← ringKrullDim_eq_of_ringEquiv e]
  obtain ⟨hq𝔪S, hq0S, hdomS, hdvrS⟩ :=
    natCast_mem_maximalIdeal_and_isDiscreteValuationRing_stalk_quotient p M H hpM hj 𝔛 y hdimS
  haveI := hdomS
  haveI := hdvrS

  have hq𝔪 : (p : A) ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (p : (X p (ΓN p M H hpM) hj).presheaf.stalk y) := heq ▸ hu.map e
    exact (IsLocalRing.mem_maximalIdeal _).mp hq𝔪S hu'
  have hq0 : (p : A) ≠ 0 := by
    intro h0
    apply hq0S
    rw [← heq, h0, map_zero]
  have hspan : Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk y)} = (Ideal.span {(p : A)}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x => Ideal.span {x}) heq.symm
  let ebar : A ⧸ Ideal.span {(p : A)} ≃+*
      (X p (ΓN p M H hpM) hj).presheaf.stalk y ⧸ Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk y)} :=
    Ideal.quotientEquiv (Ideal.span {(p : A)}) (Ideal.span {(p : (X p (ΓN p M H hpM) hj).presheaf.stalk y)}) e hspan
  haveI : IsDomain (A ⧸ Ideal.span {(p : A)}) := ebar.toMulEquiv.isDomain _
  haveI : IsDiscreteValuationRing (A ⧸ Ideal.span {(p : A)}) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ebar.symm

  haveI hmaxR := isMaximal_span_natCast_R p
  have hred : IsReduced (Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U) ⧸ Ideal.span {(p : Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U))}) := by
    letI : Field (R p ⧸ Ideal.span {(p : R p)}) := Ideal.Quotient.field _
    haveI : CharP (R p ⧸ Ideal.span {(p : R p)}) p :=
      CharP.quotient (R p) p (mem_nonunits_iff.mpr fun hu => hmaxR.ne_top (Ideal.span_singleton_eq_top.mpr hu))
    obtain ⟨A, hA, ρ, hρ⟩ := exists_place p
    haveI : CharP (IsLocalRing.ResidueField ↥A) p := charP_residueField_of_liesOverPrime p A hA
    haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
    let φ : R p →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp ρ
    have hφ : φ (p : R p) = 0 := by
      show IsLocalRing.residue ↥A (ρ (p : R p)) = 0
      rw [map_natCast, IsLocalRing.residue_eq_zero_iff]
      exact natCast_mem_maximalIdeal_of_liesOverPrime p A hA
    haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) φ) := 𝔛.fibre_reduced A hA ρ hρ
    have hV : IsAffineOpen (𝔛.π.1 ⁻¹ᵁ U) := hU.preimage 𝔛.π.1
    have h := AlgebraicGeometry.isReduced_sections_quotient_of_isReduced_pullback φ (p : R p) hφ hmaxR
      (toBase p (ΓM M H) hj) (𝔛.π.1 ⁻¹ᵁ U) hV
    first
      | (rw [map_natCast] at h; exact h)
      | (rw [map_natCast] at h; convert h using 2 <;> first | rfl | simp)
      | (simp only [map_natCast] at h; convert h using 3 <;> first | rfl | simp)

  have hinj' : Function.Injective (algebraMap Γ(X p (ΓN p M H hpM) hj, U) Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U)) := hinj
  exact free_localizedModule_of_dim_two hinj' p hred hnomax hchain (𝔭 U hU y hy) hq𝔪 hq0

theorem free_M [IsFinite 𝔛.π.1]
    (hdomA : IsDomain Γ(X p (ΓN p M H hpM) hj, U)) (hdomB : IsDomain Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U))
    (hinj : Function.Injective (𝔛.π.1.app U).hom)
    (hnomax : NoMaxMin Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U) p) (hchain : NoChain Γ(X p (ΓN p M H hpM) hj, U) p) :
    letI := algB₀ 𝔛 U
    Module.Free (Localization.AtPrime (𝔭 U hU y hy))
      (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U)) := by
  letI := algB₀ 𝔛 U
  by_cases hdim : ringKrullDim (Localization.AtPrime (𝔭 U hU y hy)) ≤ 1
  · haveI := isRegularLocalRing_A 𝔛 U hU y hy
    haveI := hdomA
    haveI : IsDomain (Localization.AtPrime (𝔭 U hU y hy)) := inferInstance
    haveI := finite_B₀ 𝔛 U hU
    haveI : Module.Finite (Localization.AtPrime (𝔭 U hU y hy))
        (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(X p (ΓM M H) hj, 𝔛.π.1 ⁻¹ᵁ U)) := inferInstance
    haveI := isTorsionFree_M 𝔛 U hU y hy hdomA hdomB hinj
    exact L1_free_of_dim_le_one hdim _
  · exact free_M_of_not_dim_le_one 𝔛 U hU y hy hdomA hdomB hinj hnomax hchain hdim

end PerPoint

theorem main {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsFinite 𝔛.π.1] : Flat 𝔛.π.1 := by
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : LocallyOfFinitePresentation (toBase p (ΓM M H) hj) := 𝔛.lfp
  haveI : SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj) := 𝔛.smooth0
  haveI : Smooth (toBase p (ΓN p M H hpM) hj) := SmoothOfRelativeDimension.smooth 1 _
  haveI : LocallyOfFinitePresentation (toBase p (ΓN p M H hpM) hj) := inferInstance
  haveI : IsLocallyNoetherian (X p (ΓN p M H hpM) hj) := LocallyOfFiniteType.isLocallyNoetherian (toBase p (ΓN p M H hpM) hj)
  refine (flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule 𝔛.π.1 fun y => ?_).1
  have hcov := twoChartCover (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
  have hyU : y ∈ chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) ⊔ chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) := by
    rw [hcov]; trivial
  rcases hyU with hy | hy
  · refine ⟨_, isAffineOpen_chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj), hy, free_M 𝔛 _ _ y hy ?_ ?_ ?_ ?_ ?_⟩
    · exact isDomain_sections_of_eq_chartFinOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) _ rfl
    · exact isDomain_sections_of_eq_chartFinOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) _ (preimage_chartFinOpen 𝔛)
    · exact injective_app_chartFinOpen 𝔛
    · exact (noMaxMin_noChain_sections_of_eq_chartFinOpen p (ΓM M H) hj _ (preimage_chartFinOpen 𝔛)).1
    · exact (noMaxMin_noChain_sections_of_eq_chartFinOpen p (ΓN p M H hpM) hj _ rfl).2
  · refine ⟨_, isAffineOpen_chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj), hy, free_M 𝔛 _ _ y hy ?_ ?_ ?_ ?_ ?_⟩
    · exact isDomain_sections_of_eq_chartInfOpen (R p) (KΓ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) _ rfl
    · exact isDomain_sections_of_eq_chartInfOpen (R p) (KΓ (ΓM M H)) (jAt (ΓM M H) hj) _ (preimage_chartInfOpen 𝔛)
    · exact injective_app_chartInfOpen 𝔛
    · exact (noMaxMin_noChain_sections_of_eq_chartInfOpen p (ΓM M H) hj _ (preimage_chartInfOpen 𝔛)).1
    · exact (noMaxMin_noChain_sections_of_eq_chartInfOpen p (ΓN p M H hpM) hj _ rfl).2

end ModularCurve.XHDRModelAtP.FlatPiH

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC transcendental_jq XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one XHDRLevel.isIntegral_X"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "pi_chartInf iota0_spec iotaInf fibre_reduced iotaInf_spec π lfp pi_chart smooth0 iota0 mk flat comp isFinite_and_locallyOfFinitePresentation_pi exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one"
namespace FlatPiH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

theorem surjective_of_isFinite_of_genericPoint {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [IsFinite π]
    (φ : Y.functionField →+* X.functionField)
    (hφ : X.fromSpecStalk (genericPoint X) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)) :
    Function.Surjective π.base := by
  have hgen : π.base (genericPoint X) = genericPoint Y := by
    have h := congrArg (fun f => f.base (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)))) hφ
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply, Scheme.fromSpecStalk_closedPoint] at h
    rw [h]
    have : (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))) =
        IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)) := Subsingleton.elim _ _
    rw [this, Scheme.fromSpecStalk_closedPoint]
  have hclosed : IsClosed (Set.range π.base) := π.isClosedMap.isClosed_range
  have hdense : closure ({genericPoint Y} : Set Y) ⊆ Set.range π.base :=
    hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, hgen⟩)
  have huniv : closure ({genericPoint Y} : Set Y) = Set.univ := (genericPoint_spec Y).def
  intro y
  exact hdense (huniv ▸ Set.mem_univ y)

end ModularCurve.XHDRModelAtP.FlatPiH

open NeronModelInfra _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.AlgebraicCurve IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
open scoped MatrixGroups in
open ModularCurve.XHDRModelAtP.FlatPiH in
set_option maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃ (_ : IsFinite 𝔛.π.1) (_ : LocallyOfFinitePresentation 𝔛.π.1), Flat 𝔛.π.1 ∧
      ∀ x : ↥(X p (ΓN p M H hpM) hj), 𝔛.π.1.finrank x = p + 1 := by
  obtain ⟨hfin, hlfp⟩ := ModularCurve.XHDRModelAtP.isFinite_and_locallyOfFinitePresentation_pi p M H hpM hpM2 hHp hj 𝔛
  haveI := hfin; haveI := hlfp
  haveI hflat : Flat 𝔛.π.1 := ModularCurve.XHDRModelAtP.FlatPiH.main 𝔛
  refine ⟨hfin, hlfp, hflat, fun x => ?_⟩
  haveI : IsIntegral (X p (ΓM M H) hj) := ModularCurve.XHDRLevel.isIntegral_X p (ΓM M H) hj
  haveI : IsIntegral (X p (ΓN p M H hpM) hj) := ModularCurve.XHDRLevel.isIntegral_X p (ΓN p M H hpM) hj
  obtain ⟨φ, hφ, -, hdeg⟩ :=
    ModularCurve.XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one p M H hpM hpM2 hHp hj 𝔛
  rw [← hdeg]
  exact Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict 𝔛.π.1
    (surjective_of_isFinite_of_genericPoint 𝔛.π.1 φ hφ) φ hφ ⊤ x trivial

end S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi (solution)
