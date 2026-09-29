-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/914f2cf2-4aa6-50e7-8f88-b56aca75be20

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_smooth_pullback_snd_toBase_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve~DRModelPackageLevel ModularCurve.XHDRLevel"

open scoped MatrixGroups

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace FwfH

noncomputable section

open IsLocalRing

theorem exists_ringHom_charP_of_not_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    {k : Type} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p)))
    (hns : ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) s)) :
    ∃ (toκ : R p →+* k) (_ : CharP k p), s = Spec.map (CommRingCat.ofHom toκ) := by
  classical
  let toκ : R p →+* k := (Spec.preimage s).hom
  have hs : Spec.map (CommRingCat.ofHom toκ) = s := by
    simp only [toκ, CommRingCat.ofHom_hom, Spec.map_preimage]
  letI : Algebra (R p) k := toκ.toAlgebra
  have hpp : p.Prime := Fact.out
  rcases GaloisRep.charZero_or_charP_of_algebra_ratLocalizedAt p k with h0 | hq
  · exfalso
    apply hns
    haveI := h0
    haveI := GaloisRep.isFractionRing_ratLocalizedAt p
    haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
    haveI := GaloisRep.ratLocalizedAt.isLocalRing hpp
    have hinj : Function.Injective toκ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      by_contra hne
      have hprime : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
      have hmax : (RingHom.ker toκ).IsMaximal := by
        haveI := hprime
        exact IsPrime.to_maximal_ideal hne
      have heq : RingHom.ker toκ = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
      have hqmem : ((p : ℕ) : R p) ∈ RingHom.ker toκ := by
        rw [heq, GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hpp]
        exact Ideal.subset_span rfl
      rw [RingHom.mem_ker, map_natCast] at hqmem
      exact hpp.ne_zero ((Nat.cast_eq_zero (R := k)).mp hqmem)
    let f : ℚ →+* k := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap (R p) ℚ) = toκ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hs' : s = Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)) := by
      rw [← hs, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
    rw [hs']
    haveI := 𝔛.smooth_generic
    have hsnd : pullback.snd (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))) =
        (pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))
          (Spec.map (CommRingCat.ofHom f))).inv ≫
        pullback.snd (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))
          (Spec.map (CommRingCat.ofHom f)) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd, Iso.inv_hom_id_assoc]
    rw [hsnd]
    infer_instance
  · exact ⟨toκ, hq, hs.symm⟩

theorem ringHom_ext_charP (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] (f g : R p →+* k) : f = g := by
  apply RingHom.ext
  intro x
  have hx : (x : ℚ).den.Coprime p := x.2
  have hden : (((x : ℚ).den : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro h
    have := Nat.Coprime.eq_one_of_dvd (hx.symm) |> fun e => e h
    exact (Fact.out : p.Prime).one_lt.ne' this

  have hnum : (((x : ℚ).num : ℚ)).den.Coprime p := by simp
  have hden' : ((((x : ℚ).den : ℕ) : ℚ)).den.Coprime p := by simp
  have hmul : x * ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ⟨((x : ℚ).num : ℚ), hnum⟩ := by
    apply Subtype.ext
    show (x : ℚ) * ((x : ℚ).den : ℚ) = ((x : ℚ).num : ℚ)
    exact Rat.mul_den_eq_num (x : ℚ)
  have hf := congrArg f hmul
  have hg := congrArg g hmul
  rw [map_mul] at hf hg
  have hfd : f ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ((x : ℚ).den : k) := by
    rw [show (⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ : R p) = (((x : ℚ).den : ℕ) : R p) from Subtype.ext (by simp), map_natCast]
  have hgd : g ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ((x : ℚ).den : k) := by
    rw [show (⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ : R p) = (((x : ℚ).den : ℕ) : R p) from Subtype.ext (by simp), map_natCast]
  have hfn : f ⟨((x : ℚ).num : ℚ), hnum⟩ = ((x : ℚ).num : k) := by
    rw [show (⟨((x : ℚ).num : ℚ), hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) from Subtype.ext (by simp), map_intCast]
  have hgn : g ⟨((x : ℚ).num : ℚ), hnum⟩ = ((x : ℚ).num : k) := by
    rw [show (⟨((x : ℚ).num : ℚ), hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) from Subtype.ext (by simp), map_intCast]
  rw [hfd, hfn] at hf
  rw [hgd, hgn] at hg
  exact mul_right_cancel₀ hden (hf.trans hg.symm)

section ValRing

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

include hA in
theorem natCast_mem_maximalIdeal : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA

include hA in

theorem charP_residueField : CharP (ResidueField ↥A) p := by
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_
  rw [← map_natCast (residue ↥A), residue_eq_zero_iff]
  exact natCast_mem_maximalIdeal p A hA

include hA in

theorem isUnit_natCast_of_coprime {n : ℕ} (hn : n.Coprime p) : IsUnit ((n : ℕ) : ↥A) := by
  by_contra hnu
  have hmem : ((n : ℕ) : ↥A) ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr hnu
  have hp := natCast_mem_maximalIdeal p A hA
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (n : ℤ) + b * (p : ℤ) = 1 := by
    refine ⟨Int.gcdA n p, Int.gcdB n p, ?_⟩
    have := Int.gcd_eq_gcd_ab (n : ℤ) (p : ℤ)
    rw [Int.gcd_natCast_natCast, hn] at this
    push_cast at this
    linarith
  have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
    have : (a : ↥A) * (n : ℕ) + (b : ↥A) * (p : ℕ) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ↥A)) hab
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp)
  exact (maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

include hA in

theorem mem_of_liesOverPrime (x : R p) : algebraMap ℚ (AlgebraicClosure ℚ) (x : ℚ) ∈ A := by
  have hx : (x : ℚ).den.Coprime p := x.2
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime p A hA hx
  have hq : (x : ℚ) = ((x : ℚ).num : ℚ) * (((x : ℚ).den : ℚ))⁻¹ := by
    rw [← div_eq_mul_inv, Rat.num_div_den]
  rw [hq, map_mul, map_inv₀, map_intCast, map_natCast]
  refine A.toSubring.mul_mem (intCast_mem A.toSubring _) ?_
  have : ((((x : ℚ).den : ℕ) : AlgebraicClosure ℚ))⁻¹ = ((↑(u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) := by
    apply inv_eq_of_mul_eq_one_right
    have h1 : (((x : ℚ).den : ℕ) : AlgebraicClosure ℚ) = ((↑u : ↥A) : AlgebraicClosure ℚ) := by
      rw [hu]; rfl
    rw [h1]
    show ((↑u : ↥A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : ↥A) : AlgebraicClosure ℚ) = 1
    rw [← show (((↑u * ↑u⁻¹ : ↥A)) : AlgebraicClosure ℚ) = ((↑u : ↥A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : ↥A) : AlgebraicClosure ℚ) from rfl,
      Units.mul_inv]
    rfl
  rw [this]
  exact SetLike.coe_mem _

end ValRing

section Embed

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

noncomputable def rho : R p →+* ↥A :=
  ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (GaloisRep.ratLocalizedAt p).subtype).codRestrict A.toSubring
    (fun x => mem_of_liesOverPrime p A hA x)

theorem rho_spec : A.subtype.comp (rho p A hA) = algebraMap (R p) (AlgebraicClosure ℚ) := by
  ext x
  rfl

include hA in

theorem isAlgebraic_residueField :
    letI := charP_residueField p A hA
    letI := ZMod.algebra (ResidueField ↥A) p
    Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) := by
  letI := charP_residueField p A hA
  letI := ZMod.algebra (ResidueField ↥A) p
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y

  have halgQ : IsAlgebraic ℚ ((x : ↥A) : AlgebraicClosure ℚ) := by
    have h := @Algebra.IsAlgebraic.isAlgebraic ℚ (AlgebraicClosure ℚ) _ _ _ (AlgebraicClosure.isAlgebraic ℚ)
      ((x : ↥A) : AlgebraicClosure ℚ)
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  have halgZ : IsAlgebraic ℤ ((x : ↥A) : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨f, hf0, hfx⟩ := halgZ
  set g := f.primPart with hg
  have hgprim : g.IsPrimitive := f.isPrimitive_primPart
  have hgx : Polynomial.aeval ((x : ↥A) : AlgebraicClosure ℚ) g = 0 := by
    have h := f.eq_C_content_mul_primPart
    rw [h, map_mul, Polynomial.aeval_C] at hfx
    rcases mul_eq_zero.mp hfx with h1 | h1
    · exfalso
      rw [eq_intCast, Int.cast_eq_zero, Polynomial.content_eq_zero_iff] at h1
      exact hf0 h1
    · exact h1

  have hgA : Polynomial.aeval x g = 0 := by
    apply A.subtype_injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int (A.subtype.comp (algebraMap ℤ ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ)), ← Polynomial.aeval_def]
    exact hgx
  have hgres : Polynomial.eval₂ (algebraMap ℤ (ResidueField ↥A)) (residue ↥A x) g = 0 := by
    have := congrArg (residue ↥A) hgA
    rwa [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int ((residue ↥A).comp (algebraMap ℤ ↥A)) (algebraMap ℤ (ResidueField ↥A))] at this

  set gp : Polynomial (ZMod p) := g.map (Int.castRingHom (ZMod p)) with hgp
  have hgp0 : gp ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ g := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have : gp.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [hgp, Polynomial.coeff_map, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have hu := (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hgprim) (p : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact (Fact.out : p.Prime).one_lt.ne' hu
  refine ⟨gp, hgp0, ?_⟩
  rw [Polynomial.aeval_def, hgp, Polynomial.eval₂_map,
    RingHom.ext_int ((algebraMap (ZMod p) (ResidueField ↥A)).comp (Int.castRingHom (ZMod p))) (algebraMap ℤ (ResidueField ↥A))]
  exact hgres

include hA in

theorem exists_ringHom_residueField (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ ι : ResidueField ↥A →+* k, True := by
  letI := charP_residueField p A hA
  letI := ZMod.algebra (ResidueField ↥A) p
  letI := ZMod.algebra k p
  haveI := isAlgebraic_residueField p A hA
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := ResidueField ↥A) (M := k) : ResidueField ↥A →ₐ[ZMod p] k).toRingHom, trivial⟩

end Embed

section Place

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)

theorem sectionFibre_fst (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    sectionFibre ε toκ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
      Spec.map (CommRingCat.ofHom toκ) ≫ ε.1 :=
  pullback.lift_fst _ _ _

theorem sectionFibre_snd (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    sectionFibre ε toκ ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem fibreMap_fst (φ : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ≫ φ.1 := by
  unfold fibreMap
  rw [pullback.lift_fst]

theorem fibreMap_snd (φ : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
      pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) := by
  unfold fibreMap
  rw [pullback.lift_snd, Category.comp_id]

include 𝔛 in

theorem preimage_w_smoothLocus : 𝔛.w.hom ⁻¹ᵁ 𝔛.smoothLocus = 𝔛.smoothLocus := by
  have hle : ∀ (g : X p (ΓM M H) hj ⟶ X p (ΓM M H) hj), g ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj → IsIso g →
      g ⁻¹ᵁ 𝔛.smoothLocus ≤ 𝔛.smoothLocus := by
    intro g hg hiso
    apply 𝔛.smoothLocus_maximal
    have e : (g ⁻¹ᵁ 𝔛.smoothLocus).ι ≫ toBase p (ΓM M H) hj = (g ∣_ 𝔛.smoothLocus) ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hg]
    rw [e]
    haveI : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := SmoothOfRelativeDimension.smooth 1 _
    infer_instance
  have hinv_over : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, 𝔛.w_over]
  apply le_antisymm (hle 𝔛.w.hom 𝔛.w_over inferInstance)
  calc 𝔛.smoothLocus = (𝔛.w.hom ≫ 𝔛.w.inv) ⁻¹ᵁ 𝔛.smoothLocus := by rw [Iso.hom_inv_id]; rfl
    _ = 𝔛.w.hom ⁻¹ᵁ (𝔛.w.inv ⁻¹ᵁ 𝔛.smoothLocus) := by rw [Scheme.Hom.comp_preimage]
    _ ≤ 𝔛.w.hom ⁻¹ᵁ 𝔛.smoothLocus := Scheme.Hom.preimage_mono _ (hle 𝔛.w.inv hinv_over inferInstance)

theorem preimage_fibreMap_w_traceU {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ ⁻¹ᵁ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus := by
  rw [← Scheme.Hom.comp_preimage, fibreMap_fst, Scheme.Hom.comp_preimage]
  show _ ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ 𝔛.smoothLocus) = _
  rw [preimage_w_smoothLocus]

theorem sectionFibre_εinf_comp_fibreMap_w {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    sectionFibre 𝔛.εinf toκ ≫ fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ = sectionFibre 𝔛.εzero toκ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, ← Category.assoc, sectionFibre_fst, sectionFibre_fst, Category.assoc]
    show _ ≫ 𝔛.εinf.1 ≫ 𝔛.w.hom = _
    rw [𝔛.w_sections]
  · rw [Category.assoc, fibreMap_snd, sectionFibre_snd, sectionFibre_snd]

theorem sectionFibre_mem_traceU (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (hε : Set.range ε.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) {κ : Type} [Field κ] (toκ : R p →+* κ) :
    (sectionFibre ε toκ).base (IsLocalRing.closedPoint κ) ∈
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus : (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) :
        Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) := by
  show (sectionFibre ε toκ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))).base (IsLocalRing.closedPoint κ) ∈
    (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
  rw [sectionFibre_fst]
  exact hε ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ), rfl⟩

include hpM2 in

theorem place
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    letI toκ := (residue ↥A).comp ρ
    (∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ),
      y ∈ connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))
          ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint (ResidueField ↥A))) →
      (fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ).base y ∈
        ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) \
        connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))
          ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∧
    (sectionFibre 𝔛.εzero toκ).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
        (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) \
      connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
        (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))
        ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint (ResidueField ↥A))) := by
  classical
  set toκ := (residue ↥A).comp ρ with htoκ
  haveI := 𝔛.isProper0; haveI := 𝔛.smooth0; haveI := 𝔛.flat; haveI := 𝔛.lfp; haveI := 𝔛.isProper

  set UU : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ) :=
    ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
      (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) with hUU
  set pinf := (sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint (ResidueField ↥A)) with hpinf

  let C₀ : Scheme.{0} := fibre (Γ := ΓN p M H hpM) (hj := hj) toκ
  let c₀ : C₀ ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom toκ))
  haveI hp0 : IsProper c₀ := inferInstance
  haveI hs0 : SmoothOfRelativeDimension 1 c₀ := inferInstance
  haveI : IsIntegral C₀ := by
    haveI := 𝔛.efib_iso A hA ρ hρ
    haveI : IsIntegral (𝔛.Mfib A hA ρ hρ).C := (𝔛.Mfib A hA ρ hρ).isIntegral
    exact IsIntegral.of_isIso (𝔛.efib A hA ρ hρ)
  haveI : LocallyOfFiniteType c₀ := inferInstance
  haveI hgi0 : GeometricallyIntegral c₀ := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed c₀

  let i₁ : SchemeHomOver c₀ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    ⟨𝔛.comp A hA ρ hρ 0, 𝔛.comp_over A hA ρ hρ 0⟩
  let i₂ : SchemeHomOver c₀ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    ⟨𝔛.comp A hA ρ hρ 1, 𝔛.comp_over A hA ρ hρ 1⟩
  haveI : IsClosedImmersion i₁.1 := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI : IsClosedImmersion i₂.1 := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  have hred : IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) := 𝔛.fibre_reduced A hA ρ hρ

  have hq1 : pinf ∈ Set.range (𝔛.comp A hA ρ hρ 0).base := 𝔛.εinf_mem_comp0 A hA ρ hρ ⟨IsLocalRing.closedPoint _, rfl⟩
  have hqU : pinf ∈ UU := sectionFibre_mem_traceU p M H hpM hj 𝔛 𝔛.εinf 𝔛.εinf_mem_smoothLocus toκ

  haveI : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := SmoothOfRelativeDimension.smooth 1 _

  have hns : ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    ModularCurve.XHDRModelAtP.not_smooth_pullback_snd_toBase_of_charP p M H hpM hj 𝔛 (ResidueField ↥A) _

  have hnotiso : ∀ (i : Fin 2), ¬ Function.Surjective (𝔛.comp A hA ρ hρ i).base := by
    intro i hsurj
    haveI : Surjective (𝔛.comp A hA ρ hρ i) := ⟨hsurj⟩
    haveI : IsClosedImmersion (𝔛.comp A hA ρ hρ i) := 𝔛.comp_isClosedImmersion A hA ρ hρ i
    haveI := hred
    haveI : IsIso (𝔛.comp A hA ρ hρ i) := isIso_of_isClosedImmersion_of_surjective _
    apply hns
    have : pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
        inv (𝔛.comp A hA ρ hρ i) ≫ c₀ := by
      rw [IsIso.eq_inv_comp, 𝔛.comp_over A hA ρ hρ i]
    rw [this]
    infer_instance
  have hne₁ : ¬ Set.range i₁.1.base ⊆ Set.range i₂.1.base := fun h => hnotiso 1 (by
    intro z
    rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with hz | hz
    · exact h hz
    · exact hz)
  have hne₂ : ¬ Set.range i₂.1.base ⊆ Set.range i₁.1.base := fun h => hnotiso 0 (by
    intro z
    rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with hz | hz
    · exact hz
    · exact h hz)

  obtain ⟨-, hcc0, hcc1, -, -⟩ :=
    AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (toBase p (ΓM M H) hj) 𝔛.smoothLocus 𝔛.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) hred
      c₀ c₀ i₁ i₂ (𝔛.comp_jointly_surjective A hA ρ hρ) hne₁ hne₂ pinf hq1 hqU

  have hfar : ∀ z : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ), z ∈ Set.range (𝔛.comp A hA ρ hρ 1).base → z ∈ UU →
      z ∈ UU \ connectedComponentIn UU pinf := by
    intro z hz1 hzU
    have : z ∈ Set.range (𝔛.comp A hA ρ hρ 1).base ∩ UU := ⟨hz1, hzU⟩
    rwa [hcc1] at this

  have hw01 : ∀ y0, (fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ).base ((𝔛.comp A hA ρ hρ 0).base y0) =
      (𝔛.comp A hA ρ hρ 1).base y0 := by
    intro y0
    rw [← Scheme.Hom.comp_apply, 𝔛.comp_w A hA ρ hρ]
  refine ⟨fun y hy => ?_, ?_⟩
  ·
    have hy' : y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∩ UU := by rw [hcc0]; exact hy
    obtain ⟨⟨y0, rfl⟩, hyU⟩ := hy'
    apply hfar
    · exact ⟨y0, (hw01 y0).symm⟩
    ·
      show (fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ).base ((𝔛.comp A hA ρ hρ 0).base y0) ∈ UU
      rw [hUU, ← preimage_fibreMap_w_traceU p M H hpM hj 𝔛 toκ] at hyU
      exact hyU
  ·
    apply hfar
    · obtain ⟨a, ha⟩ := hq1
      refine ⟨a, ?_⟩
      rw [← hw01 a, ha, hpinf, ← Scheme.Hom.comp_apply, sectionFibre_εinf_comp_fibreMap_w]
    · exact sectionFibre_mem_traceU p M H hpM hj 𝔛 𝔛.εzero 𝔛.εzero_mem_smoothLocus toκ

end Place

section General

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)

def proj {κ₀ κ : Type} [CommRing κ₀] [CommRing κ] (toκ₀ : R p →+* κ₀) (ι : κ₀ →+* κ) (toκ : R p →+* κ) (h : toκ = ι.comp toκ₀) :
    fibre (Γ := ΓM M H) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ₀ :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ι)) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h])

variable {κ₀ κ : Type} [Field κ₀] [Field κ] (toκ₀ : R p →+* κ₀) (ι : κ₀ →+* κ) (toκ : R p →+* κ) (h : toκ = ι.comp toκ₀)

theorem proj_fst : proj p M H hj toκ₀ ι toκ h ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ₀)) =
    pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) := by
  unfold proj
  rw [pullback.lift_fst, Category.comp_id]

theorem proj_snd : proj p M H hj toκ₀ ι toκ h ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ₀)) =
    pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ≫ Spec.map (CommRingCat.ofHom ι) := by
  unfold proj
  rw [pullback.lift_snd]

theorem fibreMap_proj (φ : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj)) :
    fibreMap φ toκ ≫ proj p M H hj toκ₀ ι toκ h = proj p M H hj toκ₀ ι toκ h ≫ fibreMap φ toκ₀ := by
  apply pullback.hom_ext
  · rw [Category.assoc, proj_fst, fibreMap_fst, Category.assoc, fibreMap_fst, ← Category.assoc, proj_fst]
  · rw [Category.assoc, proj_snd, ← Category.assoc, fibreMap_snd, Category.assoc, fibreMap_snd, proj_snd]

theorem sectionFibre_proj (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)) :
    sectionFibre ε toκ ≫ proj p M H hj toκ₀ ι toκ h = Spec.map (CommRingCat.ofHom ι) ≫ sectionFibre ε toκ₀ := by
  apply pullback.hom_ext
  · rw [Category.assoc, proj_fst, sectionFibre_fst, Category.assoc, sectionFibre_fst, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← h]
  · rw [Category.assoc, proj_snd, ← Category.assoc, sectionFibre_snd, Category.assoc, sectionFibre_snd, Category.id_comp,
      Category.comp_id]

theorem sectionFibre_proj_base (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)) :
    (proj p M H hj toκ₀ ι toκ h).base ((sectionFibre ε toκ).base (IsLocalRing.closedPoint κ)) =
      (sectionFibre ε toκ₀).base (IsLocalRing.closedPoint κ₀) := by
  rw [← Scheme.Hom.comp_apply, sectionFibre_proj, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

include hpM2 in

theorem general (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : R p →+* κ) :
    (∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ),
      y ∈ connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))
          ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint κ)) →
      (fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ).base y ∈
        ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) \
        connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))
          ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint κ))) ∧
    (sectionFibre 𝔛.εzero toκ).base (IsLocalRing.closedPoint κ) ∈
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
        (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) \
      connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
        (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))
        ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint κ)) := by
  classical

  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p :=
    ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := charP_residueField p A hA
  let ρ := rho p A hA
  have hρ := rho_spec p A hA
  obtain ⟨ι, -⟩ := exists_ringHom_residueField p A hA κ
  set toκ₀ : R p →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp ρ with htoκ₀
  have h : toκ = ι.comp toκ₀ := ringHom_ext_charP p _ _

  obtain ⟨hP1, hP2⟩ := place p M H hpM hpM2 hj 𝔛 A hA ρ hρ

  set π := proj p M H hj toκ₀ ι toκ h with hπ
  set U : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ) :=
    ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
      (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) with hU
  set U₀ : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ₀) :=
    ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ₀)) ⁻¹ᵁ 𝔛.smoothLocus :
      (fibre (Γ := ΓM M H) (hj := hj) toκ₀).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ₀)) with hU₀
  set pinf := (sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint κ) with hpinf
  set pinf₀ := (sectionFibre 𝔛.εinf toκ₀).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) with hpinf₀

  have hUU : U = π.base ⁻¹' U₀ := by
    rw [hU, hU₀, hπ]
    show ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
      (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) =
      ((proj p M H hj toκ₀ ι toκ h ⁻¹ᵁ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ₀)) ⁻¹ᵁ 𝔛.smoothLocus)) : Set _)
    rw [← Scheme.Hom.comp_preimage, proj_fst]

  have hπinf : π.base pinf = pinf₀ := sectionFibre_proj_base p M H hj toκ₀ ι toκ h 𝔛.εinf
  have hπzero : π.base ((sectionFibre 𝔛.εzero toκ).base (IsLocalRing.closedPoint κ)) =
      (sectionFibre 𝔛.εzero toκ₀).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) :=
    sectionFibre_proj_base p M H hj toκ₀ ι toκ h 𝔛.εzero

  have hpinfU : pinf ∈ U := sectionFibre_mem_traceU p M H hpM hj 𝔛 𝔛.εinf 𝔛.εinf_mem_smoothLocus toκ
  have hCC : π.base '' connectedComponentIn U pinf ⊆ connectedComponentIn U₀ pinf₀ := by
    apply IsPreconnected.subset_connectedComponentIn
    · exact (isPreconnected_connectedComponentIn).image _ π.base.hom.continuous.continuousOn
    · exact ⟨pinf, mem_connectedComponentIn hpinfU, hπinf⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hzU : z ∈ U := connectedComponentIn_subset _ _ hz
      rw [hUU] at hzU
      exact hzU

  have hπw : ∀ y, π.base ((fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ).base y) =
      (fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ₀).base (π.base y) := by
    intro y
    rw [← Scheme.Hom.comp_apply, hπ, fibreMap_proj, Scheme.Hom.comp_apply]

  have hdesc : ∀ z : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ), π.base z ∈ U₀ \ connectedComponentIn U₀ pinf₀ →
      z ∈ U \ connectedComponentIn U pinf := by
    intro z hz
    refine ⟨by rw [hUU]; exact hz.1, fun hzC => hz.2 (hCC ⟨z, hzC, rfl⟩)⟩
  refine ⟨fun y hy => hdesc _ ?_, hdesc _ ?_⟩
  · rw [hπw]
    exact hP1 _ (hCC ⟨y, hy, rfl⟩)
  · rw [hπzero]
    exact hP2

end General

section Frame

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj) (f : R p)

local notation "bcL" => baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)

variable {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))

abbrev wLs : pullback bcL s ⟶ pullback bcL s :=
  pullback.map bcL s bcL s (curveChange 𝔛.w.hom 𝔛.w_over (specMap (R p) (Localization.Away f))) (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (curveChange_snd _ _ _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm)

abbrev Us : (pullback bcL s).Opens :=
  (pullback.fst bcL s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus

omit [Field k] in
theorem not_smooth_comp [CommRing k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (hns : ¬ Smooth (pullback.snd bcL s)) :
    ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) (s ≫ specMap (R p) (Localization.Away f))) := by
  intro h
  apply hns
  have key := MorphismProperty.cancel_left_of_respectsIso @Smooth
    (pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) s).hom
    (pullback.snd (toBase p (ΓM M H) hj) (s ≫ specMap (R p) (Localization.Away f)))
  rw [pullbackLeftPullbackSndIso_hom_snd] at key
  exact key.mpr h

variable (toκ : R p →+* k) (hs : s ≫ specMap (R p) (Localization.Away f) = Spec.map (CommRingCat.ofHom toκ))

def E : pullback bcL s ≅ fibre (Γ := ΓM M H) (hj := hj) toκ :=
  pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) s ≪≫ pullback.congrHom rfl hs

@[reassoc]
theorem E_hom_fst : (E f s toκ hs).hom ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
    pullback.fst bcL s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) := by
  simp only [E, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

@[reassoc]
theorem E_hom_snd : (E f s toκ hs).hom ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
    pullback.snd bcL s := by
  simp only [E, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

theorem E_hom_preimage :
    (E f s toκ hs).hom ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ 𝔛.smoothLocus) = Us 𝔛 f s := by
  rw [← Scheme.Hom.comp_preimage, E_hom_fst]

theorem sectionFibrePoint_E (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)) :
    (sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1 ≫ (E f s toκ hs).hom = sectionFibre ε toκ := by
  apply pullback.hom_ext
  · rw [Category.assoc, E_hom_fst, sectionFibre, pullback.lift_fst, sectionFibrePoint, pullback.lift_fst_assoc, Category.assoc,
      sectionBaseChange_coe_fst, ← Category.assoc, hs]
  · rw [Category.assoc, E_hom_snd, sectionFibre, pullback.lift_snd]
    exact (sectionFibrePoint _ s).2

theorem wLs_E : wLs 𝔛 f s ≫ (E f s toκ hs).hom = (E f s toκ hs).hom ≫ fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, E_hom_fst, E_hom_fst_assoc, fibreMap, overOfIso, curveChange, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, E_hom_snd, fibreMap, pullback.lift_snd, Category.comp_id]

end Frame

end

end FwfH

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) (f : R p)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (hns : ¬ Smooth (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) :
        (∀ y : ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s),
          y ∈ connectedComponentIn
              (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) →
          (pullback.map (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s
              (curveChange 𝔛.w.hom 𝔛.w_over (specMap (R p) (Localization.Away f))) (𝟙 _) (𝟙 _)
              ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
              ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) \
            connectedComponentIn
              (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧
        ((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εzero) s).1).base (IsLocalRing.closedPoint k) ∈
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) \
            connectedComponentIn
              (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                  (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
              (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by
  classical
  obtain ⟨toκ, _i, hs⟩ := FwfH.exists_ringHom_charP_of_not_smooth p M H hpM hj 𝔛 (s ≫ specMap (R p) (Localization.Away f))
    (FwfH.not_smooth_comp (M := M) (H := H) (hj := hj) f s hns)
  haveI := _i
  have hN4 := FwfH.general p M H hpM hpM2 hj 𝔛 k toκ

  set e := FwfH.E (M := M) (H := H) (hj := hj) f s toκ hs with he
  let h : ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s) ≃ₜ ↥(fibre (Γ := ΓM M H) (hj := hj) toκ) :=
    Scheme.homeoOfIso e
  have hh : ∀ x, h x = e.hom.base x := fun _ => rfl

  have hU : h '' (FwfH.Us 𝔛 f s : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) =
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus : (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) :
        Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) := by
    rw [← FwfH.E_hom_preimage 𝔛 f s toκ hs]
    change h '' (h ⁻¹' ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
        (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ))) = _
    exact h.image_preimage _

  have hpt : ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj),
      h (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)) =
        (sectionFibre ε toκ).base (IsLocalRing.closedPoint k) := by
    intro ε
    rw [hh, ← Scheme.Hom.comp_apply, FwfH.sectionFibrePoint_E]

  have hCC : h '' connectedComponentIn (FwfH.Us 𝔛 f s : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
        (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) =
      connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
          (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) : Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) ((sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint k)) := by
    by_cases hp : ((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k) ∈
        (FwfH.Us 𝔛 f s : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
    · rw [h.image_connectedComponentIn hp, hU, hpt]
    · have hp' : (sectionFibre 𝔛.εinf toκ).base (IsLocalRing.closedPoint k) ∉
          ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus : (fibre (Γ := ΓM M H) (hj := hj) toκ).Opens) :
            Set ↥(fibre (Γ := ΓM M H) (hj := hj) toκ)) := by
        rw [← hpt, ← hU, h.injective.mem_set_image]
        exact hp
      rw [connectedComponentIn_eq_empty hp, Set.image_empty, connectedComponentIn_eq_empty hp']

  have hw : ∀ y, h ((FwfH.wLs 𝔛 f s).base y) = (fibreMap (overOfIso 𝔛.w 𝔛.w_over) toκ).base (h y) := by
    intro y
    rw [hh, hh, ← Scheme.Hom.comp_apply, FwfH.wLs_E, Scheme.Hom.comp_apply]
  refine ⟨fun y hy => ?_, ?_⟩
  · have hy' := hN4.1 (h y) (by rw [← hCC]; exact Set.mem_image_of_mem h hy)
    rw [← hw, ← hCC, ← hU, ← Set.image_diff h.injective, h.injective.mem_set_image] at hy'
    exact hy'
  · have h0 := hN4.2
    rw [← hpt 𝔛.εzero, ← hCC, ← hU, ← Set.image_diff h.injective, h.injective.mem_set_image] at h0
    exact h0

end S_ModularCurve_XHDRModelAtP_fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange (solution)
