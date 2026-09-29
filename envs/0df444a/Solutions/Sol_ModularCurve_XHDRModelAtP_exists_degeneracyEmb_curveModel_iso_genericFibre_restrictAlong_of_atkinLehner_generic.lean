-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ae2b7203-f86a-5d65-985a-bbeebc707646

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
import Theorems.Thm_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.ΓN XHDRModelAtP infSubgroup Gamma1_le_GammaH xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono qExpand coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel finiteAlong_laurentBaseChange_qExpFunctionFieldC GammaH_le_GammaH_div_infSubgroup finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC transcendental_jqModC"
namespace Meta0H
p2m_open "ModularCurve"

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply Gamma1_le_GammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

theorem restrictAlong_comp {K F₁ F₂ F₃ : Type*} [Field K] [Field F₁] [Field F₂] [Field F₃]
    [Algebra K F₁] [Algebra K F₂] [Algebra K F₃]
    (φ : F₁ →ₐ[K] F₂) (ψ : F₂ →ₐ[K] F₃) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψφ : (ψ.comp φ).toRingHom.IsIntegral) (v : Place K F₃) :
    v.restrictAlong (ψ.comp φ) hψφ = (v.restrictAlong ψ hψ).restrictAlong φ hφ :=
  Place.ext rfl

theorem finiteDimensional_adjoin_congr_inst {F : Type*} [Field F] {i₁ i₂ : Algebra ℚ F} (j : F)
    (h : letI := i₁; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F) :
    letI := i₂; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F := by
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this
  exact h

theorem transcendental_of_ringHom {A B : Type*} [Field A] [Field B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →+* B) {a : A} (h : Transcendental ℚ (f a)) : Transcendental ℚ a := by
  intro halg
  apply h
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  have := Polynomial.aeval_algHom_apply f.toRatAlgHom a P
  rw [hP, map_zero] at this
  exact this

theorem isIntegral_of_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) :
    σ.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ σ.surjective

end ModularCurve.Meta0H

open ModularCurve.Meta0H in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral),

      (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      ∃ (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
        (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
        (_ : IsIso eeta₀),

        eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
          y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
          Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y)) ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
          y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
          Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y)) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (ΓM M H).FiniteIndex := finiteIndex_GammaH M H
  haveI : (ΓN p M H hpM).FiniteIndex := finiteIndex_GammaH (M / p) (infSubgroup p M H hpM)
  have hTM : ModularGroup.T ∈ ΓM M H := T_mem_GammaH M H
  have hTN : ModularGroup.T ∈ ΓN p M H hpM := T_mem_GammaH (M / p) (infSubgroup p M H hpM)

  have hle : ΓM M H ≤ ΓN p M H hpM := ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  have hFle : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H :=
    IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hle))
  let αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) :=
    IntermediateField.inclusion hFle
  have hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun u => IntermediateField.coe_inclusion hFle u
  have hfinα : FiniteAlong (AlgebraicClosure ℚ) αH :=
    ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) hTN hTM αH
  have hαint : αH.toRingHom.IsIntegral := by
    letI := algebraAlong αH
    haveI : Module.Finite ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := hfinα
    intro x
    exact Algebra.IsIntegral.isIntegral (R := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) x

  let βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) :=
    θ.toAlgHom.comp αH
  have hθint : θ.toAlgHom.toRingHom.IsIntegral := isIntegral_of_algEquiv θ
  have hβint : βH.toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hαint hθint
  have hβq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun u => hθ (αH u) u (hαq u)

  have htj : Transcendental ℚ (jAt (ΓN p M H hpM) hj) :=
    transcendental_of_ringHom (SubringClass.subtype (qExpFunctionFieldC ℚ (ΓN p M H hpM)))
      (ModularCurve.transcendental_jqModC ℚ :
        Transcendental ℚ (SubringClass.subtype (qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)))
  have hfd0 := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (ΓN p M H hpM) hTN
    (ΓN p M H hpM) le_rfl (fun γ h => Or.inl h) (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)).1
  have hfd : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (ΓN p M H hpM) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))))
      ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) :=
    finiteDimensional_adjoin_congr_inst _ hfd0
  have hreg := ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC (ΓN p M H hpM)
  obtain ⟨Meta₀, eeta₀, hiso₀, heeta₀, -, hne₀, pin₀⟩ :=
    ModularCurve.exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
      (qExpFunctionFieldC ℚ (ΓN p M H hpM)) p (jAt (ΓN p M H hpM) hj) htj hfd hreg
  haveI := hiso₀
  haveI := hne₀

  let ι₀ : ↥(chartAlgFin p (ΓN p M H hpM) hj) → ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (ΓN p M H hpM))) := fun a =>
    ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩
  let ι : ↥(chartAlgFin p (ΓM M H) hj) → ↥(xHFunctionFieldBar M H) := fun a =>
    ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩
  have pinM : ∀ a : ↥(chartAlgFin p (ΓM M H) hj),
      𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a)))) = ι a :=
    fun a => Subtype.ext (𝔛.Meta_pin a)
  have pinN : ∀ a : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      Meta₀.ffEquiv.symm
        (Meta₀.C.germToFunctionField
          ((eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv a)))) = ι₀ a :=
    fun a => Subtype.ext (pin₀ a)
  have hΦθ : ∀ a : ↥(chartAlgFin p (ΓN p M H hpM) hj), αH (ι₀ a) = ι (𝔛.iota0 a) := by
    intro a
    apply Subtype.ext
    rw [hαq]
    show coeffEmb (AlgebraicClosure ℚ) _ = coeffEmb (AlgebraicClosure ℚ) _
    rw [𝔛.iota0_spec a]

  have hπ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y) := by
    intro y y₀ h
    exact AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
      (R p) (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)
      ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
      ι₀ ι Meta₀ eeta₀ heeta₀ hne₀ pinN 𝔛.Meta 𝔛.eeta 𝔛.heeta 𝔛.Meta_chart_nonempty pinM
      𝔛.π.1 𝔛.π.2 𝔛.iota0 𝔛.pi_chart αH hΦθ hαint hfinα y y₀ h
  refine ⟨αH, βH, hαint, hβint, hαq, hβq, Meta₀, eeta₀, hiso₀, heeta₀, hπ, ?_⟩

  intro y y₀ h

  have hinv : inv 𝔛.eeta ≫ 𝔛.Meta.toBase =
      pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [IsIso.inv_comp_eq, 𝔛.heeta]
  let q₁ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C :=
    pullback.lift (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom) (y.1 ≫ 𝔛.eeta ≫ pullback.snd _ _)
      (by simp only [Category.assoc, 𝔛.w_over]; rw [pullback.condition]) ≫ inv 𝔛.eeta
  have hq₁ : q₁ ≫ 𝔛.Meta.toBase = 𝟙 _ := by
    simp only [q₁, Category.assoc, hinv, pullback.lift_snd]
    rw [𝔛.heeta]
    exact y.2
  let y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} := ⟨q₁, hq₁⟩
  have hy₁ : y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom := by
    show q₁ ≫ 𝔛.eeta ≫ pullback.fst _ _ = _
    simp only [q₁, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hw := hwgen y₁ y hy₁.symm

  have hy₁' : y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 := by
    have := hy₁ =≫ 𝔛.π.1
    simpa only [Category.assoc] using this
  have h₁ := hπ y₁ y₀ (h.trans hy₁'.symm)
  refine h₁.trans ?_
  show Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y₁) =
    Place.restrictAlong (θ.toAlgHom.comp αH) hβint (𝔛.Meta.pointEquivPlace y)
  rw [restrictAlong_comp αH θ.toAlgHom hαint hθint hβint,
    AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul θ hθint, hw, smul_smul, ← map_mul,
    AlgEquiv.aut_mul, AlgEquiv.self_trans_symm, ← AlgEquiv.aut_one, map_one, one_smul]

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_of_atkinLehner_generic (solution)
