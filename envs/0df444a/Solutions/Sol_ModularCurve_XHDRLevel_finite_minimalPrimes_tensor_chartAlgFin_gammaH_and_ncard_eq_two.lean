-- Prove2me | solution 1 for ModularCurve.XHDRLevel.finite_minimalPrimes_tensor_chartAlgFin_gammaH_and_ncard_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ab2dd63b-dbaf-5b95-b3aa-e43650f32759

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_XHDRLevel_isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_finite_minimalPrimes_tensor_chartAlgFin_gammaH_and_ncard_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem wFrame_at_sigma (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σR : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[R p] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    [Fact (σR (jAt (ΓM M H) hj) ≠ 0)]
    [hFTfin : Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj)]
    [hFTinf : Algebra.FiniteType (R p) ↥(chartAlgInf p (ΓM M H) hj)] :
    Algebra.FiniteType (R p)
        ↥(TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) ∧
      Algebra.FiniteType (R p)
        ↥(TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) ∧
      IsSeparated (TwoChartIntegralModel.toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) ∧
      IsSeparated (toBase p (ΓM M H) hj) := by
  set F := ↥(qExpFunctionFieldC ℚ (ΓM M H)) with hF
  set j := jAt (ΓM M H) hj with hjdef

  obtain ⟨t, eFin, eInf, heFin, heInf, ht_over, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq (R p) F F j (σR j) σR rfl
  obtain ⟨t', eFin', eInf', heFin', heInf', ht'_over, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq (R p) F F (σR j) j σR.symm (σR.symm_apply_apply j)

  have hInfσ : Algebra.FiniteType (R p) ↥(TwoChartIntegralModel.chartAlgInf (R p) F (σR j)) := by
    refine hFTinf.of_surjective eInf (fun y => ⟨eInf' y, Subtype.ext ?_⟩)
    rw [heInf, heInf', AlgEquiv.apply_symm_apply]
  have hFinσ : Algebra.FiniteType (R p) ↥(TwoChartIntegralModel.chartAlgFin (R p) F (σR j)) := by
    refine hFTfin.of_surjective eFin (fun y => ⟨eFin' y, Subtype.ext ?_⟩)
    rw [heFin, heFin', AlgEquiv.apply_symm_apply]

  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsNoetherianRing (R p) := inferInstance
  haveI : IsProper (toBase p (ΓM M H) hj) := AlgebraicCurve.TwoChartIntegralModel.isProper_toBase (R p) F j
  have hSep : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
  have hSepσ : IsSeparated (TwoChartIntegralModel.toBase (R p) F (σR j)) := by
    have e : TwoChartIntegralModel.toBase (R p) F (σR j) = t.inv ≫ TwoChartIntegralModel.toBase (R p) F j := by
      rw [← ht_over, Iso.inv_hom_id_assoc]
    have hSep' : IsSeparated (TwoChartIntegralModel.toBase (R p) F j) := hSep
    rw [e]; infer_instance
  exact ⟨hInfσ, hFinσ, hSepσ, hSep⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem wInt_at_sigma (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σR : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[R p] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    [Fact (σR (jAt (ΓM M H) hj) ≠ 0)]
    [hST : @IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) Algebra.toSMul
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))).toSMul Algebra.toSMul]
    (hσj : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((σR (jAt (ΓM M H) hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ)) :
    σR (jAt (ΓM M H) hj) ∈ chartAlgFin p (ΓM M H) hj ∧
    jAt (ΓM M H) hj ∈ TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)) ∧
    (∀ y ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)),
      ∃ s ∈ chartAlgInf p (ΓM M H) hj, (∃ a ∈ chartAlgInf p (ΓM M H) hj, s = 1 + (jAt (ΓM M H) hj)⁻¹ * a) ∧
        s * y ∈ chartAlgInf p (ΓM M H) hj) ∧
    (∀ y ∈ chartAlgInf p (ΓM M H) hj,
      ∃ s ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)),
        (∃ a ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj)),
          s = 1 + (σR (jAt (ΓM M H) hj))⁻¹ * a) ∧
        s * y ∈ TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (σR (jAt (ΓM M H) hj))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hce : ∀ x : LaurentSeries ℚ, coeffEmb ℚ x = x := fun x => coeffMap_id x
  have h1 : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
    rw [hce, coe_jAt]; rfl
  have h2 : ((σR (jAt (ΓM M H) hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = coeffEmb ℚ (qExpand ℚ p jq) := by
    rw [hce, hσj]; rfl
  refine @ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand p _ ℚ _ _
    (qExpFunctionFieldC ℚ (ΓM M H)) (R p) _ _ _ _ _ hST
    (jAt (ΓM M H) hj) h1 _ (σR (jAt (ΓM M H) hj)) h2 _

namespace E2TwoComp

noncomputable def mapHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_add' x y := HahnSeries.map_add (f : R →+ S)

theorem mapHom_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    mapHom f x = x.map f := rfl

theorem mapHom_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (mapHom f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff n) h
  simpa [mapHom_apply, HahnSeries.map_coeff] using this

theorem ringHom_ratLocalizedAt_ext {p : ℕ} {S : Type*} [Ring S]
    (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  apply RingHom.ext
  intro x

  have hden : (x : ℚ).den.Coprime p := x.2
  have hd0 : (x : ℚ).den ≠ 0 := (x : ℚ).den_nz
  let d : ↥(GaloisRep.ratLocalizedAt p) := ⟨((x : ℚ).den : ℚ), by
    show (((x : ℚ).den : ℚ)).den.Coprime p; simp⟩
  let dinv : ↥(GaloisRep.ratLocalizedAt p) := ⟨(((x : ℚ).den : ℚ))⁻¹, by
    show ((((x : ℚ).den : ℚ))⁻¹).den.Coprime p
    rw [Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hd0)]; exact hden⟩
  have hdu : IsUnit d := by
    refine IsUnit.of_mul_eq_one dinv (Subtype.ext ?_)
    show ((x : ℚ).den : ℚ) * (((x : ℚ).den : ℚ))⁻¹ = 1
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd0)
  let n : ↥(GaloisRep.ratLocalizedAt p) := ⟨((x : ℚ).num : ℚ), by
    show (((x : ℚ).num : ℚ)).den.Coprime p; simp⟩
  have hxd : x * d = n := Subtype.ext (Rat.mul_den_eq_num (x : ℚ))
  have hdnat : d = ((x : ℚ).den : ↥(GaloisRep.ratLocalizedAt p)) := Subtype.ext (by push_cast; rfl)
  have hnint : n = ((x : ℚ).num : ↥(GaloisRep.ratLocalizedAt p)) := Subtype.ext (by push_cast; rfl)
  have hfd : f d = g d := by rw [hdnat, map_natCast, map_natCast]
  have hfn : f n = g n := by rw [hnint, map_intCast, map_intCast]
  have h1 : f x * f d = g x * f d := by
    rw [← map_mul, hxd, hfn, hfd, ← map_mul, hxd]
  exact (hdu.map f).mul_left_inj.mp h1

end E2TwoComp

namespace NcardTwoH

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem eq_zero_of_forall_laurentLift_apply_eq_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ZMod p)))
    (hθne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hset : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})

    (Θ : Fin 2 → (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] LaurentSeries κ))
    (hΘ : ∀ i (b : ↥(chartAlgFin p (ΓM M H) hj)),
      Θ i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = (θ i b).map (ZMod.castHom (dvd_refl p) κ))
    (x : κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) (hx : ∀ i, Θ i x = 0) :
    x = 0 := by
  classical

  obtain ⟨hred, -⟩ :=
    ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH p M H hpM hpM2 hHp hj
  set I : Ideal ↥(chartAlgFin p (ΓM M H) hj) := Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))} with hI
  have hrad : I.radical = I := Ideal.radical_eq_iff.mpr ((Ideal.isRadical_iff_quotient_reduced I).mpr hred)
  have hker : ∀ b : ↥(chartAlgFin p (ΓM M H) hj), (∀ i, θ i b = 0) → b ∈ I := by
    intro b hb
    have hmem : ∀ 𝔮 ∈ I.minimalPrimes, b ∈ 𝔮 := by
      intro 𝔮 h𝔮
      rw [hset] at h𝔮
      rcases h𝔮 with rfl | rfl
      · exact hb 0
      · exact hb 1
    rw [← hrad, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hIJ, hJ⟩
    haveI := hJ
    obtain ⟨𝔮, h𝔮, h𝔮J⟩ := Ideal.exists_minimalPrimes_le hIJ
    exact h𝔮J (hmem 𝔮 h𝔮)

  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  let B := Module.Basis.ofVectorSpace (ZMod p) κ
  have hι : (ZMod.castHom (dvd_refl p) κ : ZMod p →+* κ) = algebraMap (ZMod p) κ := RingHom.ext_zmod _ _

  have hlift : ∀ (c : ZMod p) (e : κ), ((c.val : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • e = c • e := by
    intro c e
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_natCast, ← hι, ZMod.castHom_apply, ZMod.cast_eq_val]

  have hrepr : ∀ y : κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj),
      ∃ f : (Module.Basis.ofVectorSpaceIndex (ZMod p) κ) →₀ ↥(chartAlgFin p (ΓM M H) hj), y = f.sum (fun s o => (B s) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] o) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
        refine ⟨(B.repr a).mapRange (fun c => ((c.val : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • b) (by simp), ?_⟩
        rw [Finsupp.sum_mapRange_index (by intro s; simp)]
        conv_lhs => rw [← B.linearCombination_repr a]
        rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.sum_tmul, Finsupp.sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← hlift, TensorProduct.smul_tmul]
    | add y z hy hz =>
        obtain ⟨f, rfl⟩ := hy
        obtain ⟨g, rfl⟩ := hz
        refine ⟨f + g, ?_⟩
        rw [Finsupp.sum_add_index']
        · intro s; simp
        · intro s o₁ o₂; rw [TensorProduct.tmul_add]

  obtain ⟨f, rfl⟩ := hrepr x
  have hzero : ∀ s ∈ f.support, ∀ i, θ i (f s) = 0 := by
    intro s hs i
    have h := hx i
    rw [Finsupp.sum, map_sum] at h
    have hC : ∀ a : κ, algebraMap κ (LaurentSeries κ) a = HahnSeries.single 0 a := fun a => by
      show HahnSeries.ofPowerSeries ℤ κ (PowerSeries.C a) = _
      exact HahnSeries.ofPowerSeries_C a
    have hterm : ∀ t, Θ i ((B t) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] f t) = HahnSeries.single 0 (B t) * (θ i (f t)).map (ZMod.castHom (dvd_refl p) κ) := by
      intro t
      rw [show (B t) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] f t = (algebraMap κ (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) (B t)) * ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] f t) by
            rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul, AlgHom.commutes, hΘ, hC]
    simp only [hterm] at h

    ext n
    have hn := congrArg (fun z : LaurentSeries κ => z.coeff n) h
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single_zero_mul, HahnSeries.map_coeff, HahnSeries.coeff_zero] at hn

    have hn' : ∑ t ∈ f.support, ((θ i (f t)).coeff n) • B t = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Algebra.smul_def, ← hι]; exact mul_comm _ _
    have hli := (linearIndependent_iff'.mp B.linearIndependent) f.support (fun t => (θ i (f t)).coeff n) hn' s hs
    simpa using hli

  rw [Finsupp.sum]
  refine Finset.sum_eq_zero (fun s hs => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hker (f s) (hzero s hs))
  rw [← hc, show c * ((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj)) = ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • c by
      rw [Algebra.smul_def, map_natCast]; exact mul_comm _ _,
    ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, CharP.cast_eq_zero, zero_mul, TensorProduct.zero_tmul]

end NcardTwoH

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ] :
    (minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).Finite ∧ (minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).ncard = 2 := by
  classical

  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hMp : NeZero (M / p) := neZero_div p M hpM
  have hpN : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  haveI hPID : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI hFrac : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hTM : ModularGroup.T ∈ ΓM M H := translation_mem_GammaH M H
  have hTN : ModularGroup.T ∈ ΓN p M H hpM := translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  have hsub : ΓM M H ≤ ΓN p M H hpM := ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  haveI hFI_M : (ΓM M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  haveI hFI_N : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  have hjM : ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ hj
  have hjN : ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ hj

  obtain ⟨hFTfin, hFTinf⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H) hTM (jAt (ΓM M H) hj) hjM
  obtain ⟨hFTfin0, hFTinf0⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓN p M H hpM) hTN (jAt (ΓN p M H hpM) hj) hjN
  haveI := hFTfin; haveI := hFTinf; haveI := hFTfin0; haveI := hFTinf0

  obtain ⟨σ, hσq, -⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  let σR : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[R p] ↥(qExpFunctionFieldC ℚ (ΓM M H)) := σ.restrictScalars (R p)
  haveI hσj0 : Fact (σR (jAt (ΓM M H) hj) ≠ 0) :=
    ⟨fun h => (Fact.out : jAt (ΓM M H) hj ≠ 0) (by simpa using congrArg σR.symm h)⟩
  obtain ⟨hFTinfσ, -, hSepσ, hSep⟩ := wFrame_at_sigma p M H hj σR
  haveI := hFTinfσ; haveI := hSepσ; haveI := hSep
  have hIST' : @IsScalarTower (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) Algebra.toSMul
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))).toSMul Algebra.toSMul :=
    @IsScalarTower.of_algebraMap_eq (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) _ fun x =>
        (IsScalarTower.algebraMap_apply (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) x).trans
          (RingHom.congr_fun (Subsingleton.elim _ _) _)
  have hσj : ((σR (jAt (ΓM M H) hj) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) := by
    have := hσq (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) (by rw [hjM, hjN])
    rw [hjN] at this
    exact this
  obtain ⟨hWfin, hWfin', hWvis, hWvis'⟩ := wInt_at_sigma p M H hj σR (hST := hIST') hσj
  obtain ⟨w, θc, hwover, hθc, hwchart, hwpre⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
      (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) σR hWfin hWfin' hWvis hWvis'

  obtain ⟨πX, iota0, iotaInf, hπover, hiota0, hpichart, hiotaInf, hpichartInf, hπfinite, hπsurj, hπpre⟩ :=
    ModularCurve.exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le p (ΓM M H) (ΓN p M H hpM) hsub hTM
      (jAt (ΓM M H) hj) hjM (jAt (ΓN p M H hpM) hj) hjN

  have htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((θc (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := fun b => by
    rw [hθc]
    exact hσq _ _ (hiota0 b)

  obtain ⟨θ, -, -, hθne, hset, -, -⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj iota0 hiota0 θc htheta
  have hθ : ∀ i, RingHom.ker (θ i) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
    intro i; fin_cases i
    · rw [hset]; exact Set.mem_insert _ _
    · rw [hset]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hι : Function.Injective ι := ι.injective
  let g : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →ₐ[↥(GaloisRep.ratLocalizedAt p)] LaurentSeries κ) := fun i =>
    { (E2TwoComp.mapHom ι).comp (θ i) with
      commutes' := fun r => by
        have h := E2TwoComp.ringHom_ratLocalizedAt_ext
          (((E2TwoComp.mapHom ι).comp (θ i)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin p (ΓM M H) hj)))
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (LaurentSeries κ))
        exact RingHom.congr_fun h r }
  have hg : ∀ i b, g i b = (θ i b).map ι := fun i b => rfl
  let f₀ : κ →ₐ[↥(GaloisRep.ratLocalizedAt p)] LaurentSeries κ :=
    { algebraMap κ (LaurentSeries κ) with
      commutes' := fun r => RingHom.congr_fun (E2TwoComp.ringHom_ratLocalizedAt_ext
        ((algebraMap κ (LaurentSeries κ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ)) (algebraMap ↥(GaloisRep.ratLocalizedAt p) (LaurentSeries κ))) r }
  have hf₀ : ∀ a, f₀ a = algebraMap κ (LaurentSeries κ) a := fun a => rfl
  let Θ' : Fin 2 → (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[↥(GaloisRep.ratLocalizedAt p)] LaurentSeries κ) := fun i =>
    Algebra.TensorProduct.productMap f₀ (g i)
  have hΘ' : ∀ i (a : κ) (b : ↥(chartAlgFin p (ΓM M H) hj)), Θ' i (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = algebraMap κ (LaurentSeries κ) a * (θ i b).map ι := by
    intro i a b
    simp only [Θ', Algebra.TensorProduct.productMap_apply_tmul, hf₀, hg]
  let Θ : Fin 2 → (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] LaurentSeries κ) := fun i =>
    { (Θ' i).toRingHom with
      commutes' := fun a => by
        show Θ' i (algebraMap κ (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) a) = algebraMap κ (LaurentSeries κ) a
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        show Algebra.TensorProduct.productMap f₀ (g i) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] 1) = _
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, hf₀] }
  have hΘ : ∀ i (b : ↥(chartAlgFin p (ΓM M H) hj)), Θ i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = (θ i b).map ι := by
    intro i b
    show Θ' i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = _
    rw [hΘ', map_one, one_mul]
  have hΘg : ∀ i (b : ↥(chartAlgFin p (ΓM M H) hj)),
      Θ i (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := κ) b) = g i b := by
    intro i b
    show Θ' i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = g i b
    rw [hΘ', map_one, one_mul, hg]

  have hinj : ∀ x, (∀ i, Θ i x = 0) → x = 0 := fun x hx =>
    NcardTwoH.eq_zero_of_forall_laurentLift_apply_eq_zero p M H hpM hpM2 hHp hj κ θ hθne hset Θ hΘ x hx

  let P : Fin 2 → Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) := fun i => RingHom.ker (Θ i)
  have hPprime : ∀ i, (P i).IsPrime := fun i => RingHom.ker_isPrime (Θ i)
  have hPinf : P 0 ⊓ P 1 = ⊥ := by
    refine le_bot_iff.mp (fun x hx => ?_)
    rw [Ideal.mem_bot]
    refine hinj x (fun i => ?_)
    fin_cases i
    · exact hx.1
    · exact hx.2
  have hcover : ∀ Q : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)), Q.IsPrime → P 0 ≤ Q ∨ P 1 ≤ Q := by
    intro Q hQ
    refine hQ.mul_le.mp ?_
    exact (Ideal.mul_le_inf).trans (hPinf.le.trans bot_le)

  have hcomap : ∀ i, (P i).comap (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := κ) :
      ↥(chartAlgFin p (ΓM M H) hj) →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) = RingHom.ker (θ i) := by
    intro i
    ext b
    simp only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_toRingHom, hΘg]
    constructor
    · intro h
      apply E2TwoComp.mapHom_injective ι hι
      rw [map_zero]; exact h
    · intro h
      show (E2TwoComp.mapHom ι) (θ i b) = 0
      simp [h]
  have hnotle : ∀ i j, i ≠ j → ¬ P i ≤ P j := by
    intro i j hij hle
    have hle' : RingHom.ker (θ i) ≤ RingHom.ker (θ j) := by
      have h := Ideal.comap_mono (f := (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := κ) :
        ↥(chartAlgFin p (ΓM M H) hj) →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj))) hle
      simp only [hcomap] at h
      exact h
    have hji : RingHom.ker (θ j) ≤ RingHom.ker (θ i) :=
      (hθ j).2 ⟨(hθ i).1.1, (hθ i).1.2⟩ hle'
    have heq : RingHom.ker (θ i) = RingHom.ker (θ j) := le_antisymm hle' hji
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact hθne heq
    · exact hθne heq.symm
    · exact hij rfl
  have hP01 : P 0 ≠ P 1 := fun h => hnotle 0 1 (by decide) h.le

  have hmin : ∀ i, P i ∈ minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) := by
    intro i
    refine ⟨⟨hPprime i, bot_le⟩, ?_⟩
    rintro Q ⟨hQ, -⟩ hQle
    rcases hcover Q hQ with h0 | h1
    · fin_cases i
      · exact h0
      · exact absurd (h0.trans hQle) (hnotle 0 1 (by decide))
    · fin_cases i
      · exact absurd (h1.trans hQle) (hnotle 1 0 (by decide))
      · exact h1
  have hset' : minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin p (ΓM M H) hj)) = {P 0, P 1} := by
    ext Q
    constructor
    · intro hQ
      rcases hcover Q hQ.1.1 with h0 | h1
      · have := hQ.2 ⟨hPprime 0, bot_le⟩ h0
        exact Or.inl (le_antisymm this h0)
      · have := hQ.2 ⟨hPprime 1, bot_le⟩ h1
        exact Or.inr (le_antisymm this h1)
    · rintro (rfl | rfl)
      · exact hmin 0
      · exact hmin 1
  refine ⟨?_, ?_⟩
  · rw [hset']; exact Set.toFinite _
  · rw [hset']; exact Set.ncard_pair hP01

end S_ModularCurve_XHDRLevel_finite_minimalPrimes_tensor_chartAlgFin_gammaH_and_ncard_eq_two
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_finite_minimalPrimes_tensor_chartAlgFin_gammaH_and_ncard_eq_two (solution)
