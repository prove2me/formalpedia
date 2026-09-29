-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/89f56971-9ef6-5610-ba79-89851818be0e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups

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

theorem germToFunctionField_app_eq_of_le {M X : Scheme.{u}} [IrreducibleSpace M]
    (g : M ⟶ X) (V V' : X.Opens) (h : V' ≤ V) (s : Γ(X, V))
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V))] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V'))] :
    M.germToFunctionField (g ⁻¹ᵁ V) ((g.app V).hom s) =
      M.germToFunctionField (g ⁻¹ᵁ V') ((g.app V').hom ((X.presheaf.map (homOfLE h).op).hom s)) := by
  have hle : g ⁻¹ᵁ V' ≤ g ⁻¹ᵁ V := fun x hx => h hx
  have hnat := congrArg (fun φ => φ.hom s) (g.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  rw [hnat]
  exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hle) _ _ _).symm

end ReadChartInf

namespace ReadChartFinM

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

set_option maxHeartbeats 6400000 in

theorem restrict_secFin_eq_secMid (b : ↥(chartAlgFin p Γ hj))
    (hVf : ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ≫ ιInf p Γ hj) ''ᵁ ⊤) ≤ ((ιFin p Γ hj) ''ᵁ ⊤)) :
    ((X p Γ hj).presheaf.map (homOfLE hVf).op).hom
        (((ιFin p Γ hj).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p Γ hj))).inv.hom b)) =
      (((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ≫ ιInf p Γ hj)).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of
        ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)))).inv.hom
          (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) b)) := by
  have hglue := TwoChartIntegralModel.glue_condition (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
  have hA := ReadChartInf.appLE_appIso_inv_eq (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ≫ ιInf p Γ hj) (ιFin p Γ hj) (𝟙 _)
    (TwoChartIntegralModel.fFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)) (by rw [Category.comp_id]; exact hglue.symm) hVf
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p Γ hj))).inv.hom b)
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app] at hA
  erw [hA]
  congr 1
  have h1 := congrArg (fun ψ => ψ.hom b) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (AlgHom.toRingHom (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  exact h1.symm

set_option maxHeartbeats 6400000 in

theorem restrict_secInf_eq_secMid (c : ↥(chartAlgInf p Γ hj))
    (hVi : ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ≫ ιInf p Γ hj) ''ᵁ ⊤) ≤ ((ιInf p Γ hj) ''ᵁ ⊤)) :
    ((X p Γ hj).presheaf.map (homOfLE hVi).op).hom
        (((ιInf p Γ hj).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p Γ hj))).inv.hom c)) =
      (((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ≫ ιInf p Γ hj)).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of
        ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)))).inv.hom
          (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) c)) := by
  have hA := ReadChartInf.appLE_appIso_inv_eq (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj) ≫ ιInf p Γ hj) (ιInf p Γ hj) (𝟙 _)
    (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)) (by rw [Category.comp_id]) hVi
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p Γ hj))).inv.hom c)
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app] at hA
  erw [hA]
  congr 1
  have h1 := congrArg (fun ψ => ψ.hom c) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (AlgHom.toRingHom (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  exact h1.symm

theorem exists_pow_jInv_mul_mem (b : ↥(chartAlgFin p Γ hj)) :
    ∃ n : ℕ, ((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))⁻¹) ^ n * (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ chartAlgInf p Γ hj := by
  have hsub : ({(jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))} : Set ↥(qExpFunctionFieldC ℚ Γ)) ⊆ insert ((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))⁻¹)⁻¹ {(jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))⁻¹} := by
    rw [inv_inv]
    exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  have hb : (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ TwoChartIntegralModel.chartAlg (R p) ↥(qExpFunctionFieldC ℚ Γ) (insert ((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))⁻¹)⁻¹ {(jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ))⁻¹}) :=
    TwoChartIntegralModel.chartAlg_mono (R := R p) (F := ↥(qExpFunctionFieldC ℚ Γ)) hsub b.2
  have hj0 : (jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ)) ≠ 0 := Fact.out
  exact TwoChartIntegralModel.exists_pow_mul_mem_chartAlg (R := R p) (F := ↥(qExpFunctionFieldC ℚ Γ)) (Set.mem_singleton _)
    (inv_ne_zero hj0) hb

end ReadChartFinM

set_option maxHeartbeats 12800000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))),
    ∀ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      (((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιFin p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))))
          : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

  let jI : ↥(chartAlgInf p (ΓM M H) hj) := TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
  have hjIcoe : ((jI : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (jqModC ℚ)⁻¹ := by
    show (((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = _
    push_cast
    rw [coe_jAt]

  obtain ⟨hneI, hIj⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd p M H hpM hpM2 hHp hj 𝔓 A hA ρ hρ jI
  haveI := hneI

  have hliftj : ReadChartInfM.lift p (ΓM M H) hj jI * jqModC (R p) = 1 := by
    apply ReadChartInfM.coeffMap_injective _ (IsFractionRing.injective (R p) ℚ)
    rw [map_mul, map_one, ReadChartInfM.lift_spec, hjIcoe]
    have : coeffMap (algebraMap (R p) ℚ) (jqModC (R p)) = jqModC ℚ := by
      ext n
      rw [coeffMap_coeff, coeff_jqModC_eq_intCast (R := R p), coeff_jqModC_eq_intCast (R := ℚ), map_intCast]
    rw [this, inv_mul_cancel₀ jqModC_rat_ne_zero]
  have hr0 : coeffMap ((IsLocalRing.residue ↥A).comp ρ) (ReadChartInfM.lift p (ΓM M H) hj jI) ≠ 0 := by
    intro h0
    have := congrArg (coeffMap ((IsLocalRing.residue ↥A).comp ρ)) hliftj
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hvalj : ((((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv jI))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap ((IsLocalRing.residue ↥A).comp ρ) (ReadChartInfM.lift p (ΓM M H) hj jI) := hIj _ (ReadChartInfM.lift_spec p (ΓM M H) hj jI)

  have hξI : genericPoint (𝔓.Mfib A hA ρ hρ).C ∈ ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) :=
    ((genericPoint_spec (𝔓.Mfib A hA ρ hρ).C).mem_open_set_iff (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).isOpen).mpr
      (by simpa using hneI)
  have hunit : IsUnit (((X p (ΓM M H) hj).presheaf.germ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).base (genericPoint (𝔓.Mfib A hA ρ hρ).C)) hξI).hom
      (((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv jI))) := by
    apply (isUnit_map_iff (Scheme.Hom.stalkMap ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) (genericPoint (𝔓.Mfib A hA ρ hρ).C)).hom _).mp
    rw [Scheme.Hom.germ_stalkMap_apply]
    apply isUnit_iff_ne_zero.mpr
    intro h0
    apply hr0
    rw [← hvalj]
    have h0' : ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv jI))))) = 0 := by
      change (𝔓.Mfib A hA ρ hρ).ffEquiv.symm _ = 0
      rw [h0, map_zero]
    rw [h0']
    rfl
  have hmem : ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).base (genericPoint (𝔓.Mfib A hA ρ hρ).C) ∈ ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤) := by
    have h1 := ((X p (ΓM M H) hj).mem_basicOpen _ _ hξI).mpr hunit
    rw [← Scheme.image_basicOpen, basicOpen_eq_of_affine] at h1
    obtain ⟨𝔭, h𝔭, h𝔭eq⟩ := h1
    letI := (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).toRingHom.toAlgebra
    haveI := TwoChartIntegralModel.isLocalization_away_inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    have hrange := PrimeSpectrum.localization_away_comap_range ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
      (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
    have h𝔭' : 𝔭 ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥(chartAlgInf p (ΓM M H) hj) ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)))) := by rw [hrange]; exact h𝔭
    obtain ⟨m, hm⟩ := h𝔭'
    refine ⟨m, trivial, ?_⟩
    rw [← h𝔭eq, ← hm]
    rfl
  have hVi : ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤) ≤ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) := by
    rintro x ⟨m, -, rfl⟩; exact ⟨_, trivial, rfl⟩
  have hVf : ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤) ≤ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) := by
    rintro x ⟨m, -, rfl⟩
    rw [← TwoChartIntegralModel.glue_condition]
    exact ⟨_, trivial, rfl⟩
  have hξm : genericPoint (𝔓.Mfib A hA ρ hρ).C ∈ ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤) := hmem
  haveI hneM : Nonempty (Scheme.Opens.toScheme (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤))) := ⟨⟨_, hξm⟩⟩
  haveI hneF : Nonempty (Scheme.Opens.toScheme (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := ⟨⟨_, hVf hξm⟩⟩
  refine ⟨hneF, ?_⟩
  intro y hy

  let rMid : ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) →+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
    (𝔓.Mfib A hA ρ hρ).ffEquiv.symm.toRingHom.comp
      (((𝔓.Mfib A hA ρ hρ).C.germToFunctionField (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤))).hom.comp
        ((((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).app ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom.comp
          (((((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj)).appIso ⊤).inv).hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)))).inv.hom)))
  have hFin : ∀ b' : ↥(chartAlgFin p (ΓM M H) hj), ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιFin p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b'))))) = rMid (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) b') := by
    intro b'
    show _ = (𝔓.Mfib A hA ρ hρ).ffEquiv.symm ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤))
      ((((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).app ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom ((((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj)).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)))).inv.hom (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) b')))))
    congr 1
    rw [ReadChartInf.germToFunctionField_app_eq_of_le ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) _ _ hVf]
    erw [ReadChartFinM.restrict_secFin_eq_secMid p (ΓM M H) hj b' hVf]
  have hInf : ∀ c : ↥(chartAlgInf p (ΓM M H) hj), ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv c))))) = rMid (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) c) := by
    intro c
    show _ = (𝔓.Mfib A hA ρ hρ).ffEquiv.symm ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) ⁻¹ᵁ ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤))
      ((((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).app ((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom ((((TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj)).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)))).inv.hom (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) c)))))
    congr 1
    rw [ReadChartInf.germToFunctionField_app_eq_of_le ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))) _ _ hVi]
    erw [ReadChartFinM.restrict_secInf_eq_secMid p (ΓM M H) hj c hVi]

  obtain ⟨n, hn⟩ := ReadChartFinM.exists_pow_jInv_mul_mem p (ΓM M H) hj b
  let c : ↥(chartAlgInf p (ΓM M H) hj) := ⟨_, hn⟩
  have hmid : TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) b *
      (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) jI) ^ n =
      TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) c := by
    apply Subtype.ext
    push_cast
    simp only [TwoChartIntegralModel.coe_chartIncl]
    show (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) * ((jI : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) ^ n = ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))⁻¹) ^ n * (b : ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    rw [mul_comm]
    rfl
  have hkey : ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιFin p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))))) * (((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv jI)))))) ^ n = ((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv c))))) := by
    rw [hFin, hInf, hInf, ← map_pow, ← map_mul, hmid]

  obtain ⟨hneI', hIc⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd p M H hpM hpM2 hHp hj 𝔓 A hA ρ hρ c
  have hliftc : coeffMap (algebraMap (R p) ℚ) ((ReadChartInfM.lift p (ΓM M H) hj jI) ^ n * y) = ((c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
    rw [map_mul, map_pow, ReadChartInfM.lift_spec, hy]
    show _ = ((((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))⁻¹) ^ n * (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)
    push_cast
    rfl
  have hvalc := hIc _ hliftc
  have hcoe := congrArg (fun z : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) => (z : LaurentSeries (IsLocalRing.ResidueField ↥A))) hkey
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at hcoe
  rw [hvalj, hvalc, map_mul, map_pow, mul_comm] at hcoe
  exact mul_left_cancel₀ (pow_ne_zero n hr0) hcoe

end S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib (solution)
