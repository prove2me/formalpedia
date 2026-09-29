-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ff088ccc-81aa-50e3-8739-72747f45d16a

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss
import Theorems.Thm_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical
import Theorems.Thm_ModularCurve_XHDRModelAtP_algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
import Theorems.Thm_Localization_AtPrime_mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

open scoped TensorProduct

noncomputable section

namespace BranchReadSkel

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve"
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Generic

universe u

variable {R K B : Type u} [CommRing R] [CommRing K] [CommRing B] [Algebra R K] [Algebra R B]
  {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
  (ιB : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ιB]
  (hιB : ιB ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

include hιB

omit hιB in
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop :=
  Scheme.Hom.appLE_eq_app _

noncomputable def bcChart :
    Spec (CommRingCat.of (K ⊗[R] B)) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (pullbackSpecIso R K B).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm) ≫
    (pullbackSymmetry _ _).hom

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem bcChart_fst : bcChart c ιB hιB (K := K) ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) ≫ ιB := by
  simp only [bcChart, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rfl

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem bcChart_snd : bcChart c ιB hιB (K := K) ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))) := by
  simp only [bcChart, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, Category.comp_id,
    pullbackSpecIso_inv_fst]

scoped instance bcChart_isOpenImmersion : IsOpenImmersion (bcChart c ιB hιB (K := K)) := by
  have : IsOpenImmersion (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := 𝟙 _) (i₂ := ιB) inferInstance inferInstance
      (Category.id_comp _).symm hιB.symm
  unfold bcChart
  infer_instance

omit [IsOpenImmersion ιB] in
theorem range_bcChart : Set.range (bcChart c ιB hιB (K := K)) =
    (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹' Set.range ιB := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) t, ?_⟩
    show _ = (bcChart c ιB hιB ≫ pullback.fst _ _) t
    rw [bcChart_fst]
    rfl
  · rintro z ⟨w, hw⟩
    set z' : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))) c) :=
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv z with hz'def
    have hz' : z' ∈ Set.range (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm)) := by
      rw [Scheme.Pullback.range_map]
      refine ⟨⟨pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K))) c z', rfl⟩, ⟨w, ?_⟩⟩
      show ιB w = ((pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K))) c) z
      rw [pullbackSymmetry_inv_comp_snd]
      exact hw
    obtain ⟨t, ht⟩ := hz'
    refine ⟨(pullbackSpecIso R K B).hom t, ?_⟩
    show ((pullbackSpecIso R K B).hom ≫ bcChart c ιB hιB) t = z
    simp only [bcChart, Iso.hom_inv_id_assoc, Scheme.Hom.comp_apply, ht, hz'def]
    show ((pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv ≫
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).hom) z = z
    rw [Iso.inv_hom_id]
    rfl

variable {Y : Scheme.{u}} (e : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e]

noncomputable def gChart : Spec (CommRingCat.of (K ⊗[R] B)) ⟶ Y := bcChart c ιB hιB ≫ inv e

scoped instance gChart_isOpenImmersion : IsOpenImmersion (gChart c ιB hιB e) := by
  unfold gChart; infer_instance

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem gChart_comp_fst : gChart c ιB hιB e ≫ e ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) ≫ ιB := by
  simp [gChart, bcChart_fst]

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem gChart_comp_snd : gChart c ιB hιB e ≫ e ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))) := by
  simp [gChart, bcChart_snd]

theorem opensRange_gChart :
    (gChart c ιB hιB e).opensRange = (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤) := by
  ext z
  simp only [Scheme.Hom.coe_opensRange, Set.mem_range, TopologicalSpace.Opens.map_coe, Set.mem_preimage,
    TopologicalSpace.Opens.coe_top, Scheme.Hom.coe_image, Set.image_univ]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) t, ?_⟩
    show _ = (gChart c ιB hιB e ≫ e ≫ pullback.fst _ _) t
    rw [gChart_comp_fst]
    rfl
  · rintro ⟨w, hw⟩
    have : e z ∈ Set.range (bcChart c ιB hιB (K := K)) := by
      rw [range_bcChart]
      exact ⟨w, hw⟩
    obtain ⟨t, ht⟩ := this
    refine ⟨t, ?_⟩
    show (bcChart c ιB hιB ≫ inv e) t = z
    rw [Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl

theorem isAffineOpen_U :
    IsAffineOpen ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) := by
  rw [← opensRange_gChart c ιB hιB e]; exact isAffineOpen_opensRange _

theorem top_le_preimage_U :
    ⊤ ≤ (gChart c ιB hιB e) ⁻¹ᵁ ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) := by
  rw [← opensRange_gChart c ιB hιB e, Scheme.Hom.preimage_opensRange]

noncomputable def φ : Γ(Y, (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) ⟶
    Γ(Spec (CommRingCat.of (K ⊗[R] B)), ⊤) :=
  (gChart c ιB hιB e).appLE _ ⊤ (top_le_preimage_U c ιB hιB e)

scoped instance φ_isIso : IsIso (φ c ιB hιB e) := by
  unfold φ
  rw [Scheme.Hom.appLE]
  have h1 : IsIso ((gChart c ιB hιB e).app
      ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤))) :=
    Scheme.Hom.isIso_app _ _ (by rw [opensRange_gChart c ιB hιB e])
  have h2 : homOfLE (top_le_preimage_U c ιB hιB e) =
      eqToHom (by rw [← opensRange_gChart c ιB hιB e, Scheme.Hom.preimage_opensRange]) :=
    Subsingleton.elim _ _
  rw [h2, eqToHom_op]
  infer_instance

noncomputable def θ : Γ(Y, (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) ≅
    CommRingCat.of (K ⊗[R] B) :=
  asIso (φ c ιB hιB e) ≪≫ Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))

theorem φ_section (b : B) :
    φ c ιB hιB e (((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤))
      ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) =
    (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).inv ((1 : K) ⊗ₜ[R] b) := by
  have key : ∀ {f₁ f₂ : Spec (CommRingCat.of (K ⊗[R] B)) ⟶ X} (_ : f₁ = f₂)
      (e₁ : ⊤ ≤ f₁ ⁻¹ᵁ (ιB ''ᵁ ⊤)) (e₂ : ⊤ ≤ f₂ ⁻¹ᵁ (ιB ''ᵁ ⊤)),
      f₁.appLE (ιB ''ᵁ ⊤) ⊤ e₁ = f₂.appLE (ιB ''ᵁ ⊤) ⊤ e₂ := by
    rintro _ _ rfl _ _; rfl
  have hle : ⊤ ≤ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)
      ≫ ιB) ⁻¹ᵁ (ιB ''ᵁ ⊤) := by
    rw [← gChart_comp_fst c ιB hιB e]
    exact (top_le_preimage_U c ιB hιB e)
  have h1 : (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤) ≫ φ c ιB hιB e =
      (ιB.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)).appTop := by
    unfold φ
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, key (gChart_comp_fst c ιB hιB e) _ hle,
      ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ (ιB.preimage_image_eq ⊤).ge le_top,
      Scheme.Hom.appIso_hom', appLE_top_top]
  have h2 := congrArg (fun ψ => ψ.hom ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2, Iso.inv_hom_id_apply]
  have h3 := congrArg (fun ψ => ψ.hom b) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [← h3]
  rfl

theorem θ_section (b : B) :
    (θ c ιB hιB e).hom (((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤))
      ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) = (1 : K) ⊗ₜ[R] b := by
  simp only [θ, Iso.trans_hom, asIso_hom]
  show (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).hom (φ c ιB hιB e _) = _
  rw [φ_section c ιB hιB e b, Iso.inv_hom_id_apply]

theorem φ_const (cK : Y ⟶ Spec (CommRingCat.of K))
    (hcK : gChart c ιB hιB e ≫ cK = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
    (α : K) :
    φ c ιB hιB e (Y.presheaf.map (homOfLE le_top).op (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) =
    (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).inv (α ⊗ₜ[R] (1 : B)) := by
  have h1 : Y.presheaf.map (homOfLE (le_top :
      (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤) ≤ ⊤)).op ≫ φ c ιB hιB e =
      (gChart c ιB hιB e).appTop := by
    unfold φ
    rw [Scheme.Hom.map_appLE, appLE_top_top]
  have h2 := congrArg (fun ψ => ψ.hom (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcK]
  have h3 := congrArg (fun ψ => ψ.hom α) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [← h3]
  rfl

theorem θ_const (cK : Y ⟶ Spec (CommRingCat.of K))
    (hcK : gChart c ιB hιB e ≫ cK = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
    (α : K) :
    (θ c ιB hιB e).hom (Y.presheaf.map (homOfLE le_top).op (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) =
    α ⊗ₜ[R] (1 : B) := by
  simp only [θ, Iso.trans_hom, asIso_hom]
  show (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).hom (φ c ιB hιB e _) = _
  rw [φ_const c ιB hιB e cK hcK, Iso.inv_hom_id_apply]

theorem specθ_comp_fromSpec :
    Spec.map (θ c ιB hιB e).hom ≫ (isAffineOpen_U c ιB hιB e).fromSpec = gChart c ιB hιB e := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (gChart c ιB hιB e) (isAffineOpen_U c ιB hιB e)
    (isAffineOpen_top _) (top_le_preimage_U c ιB hιB e)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  simp only [θ, Iso.trans_hom, asIso_hom, Spec.map_comp, Category.assoc]
  erw [h]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem fromSpec_specθ (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (isAffineOpen_U c ιB hιB e).fromSpec (Spec.map (θ c ιB hιB e).hom 𝔮') = gChart c ιB hιB e 𝔮' := by
  rw [← Scheme.Hom.comp_apply, specθ_comp_fromSpec]

theorem specθ_asIdeal (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (Spec.map (θ c ιB hιB e).hom 𝔮').asIdeal = 𝔮'.asIdeal.comap (θ c ιB hιB e).hom.hom := rfl

end Generic

section ChartA

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

abbrev XA : Scheme := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))

abbrev XFinA : (XA p M H hj A).Opens :=
  (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)

theorem isAffineOpen_XFinA : IsAffineOpen (XFinA p M H hj A) :=
  isAffineOpen_U (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 _)

def thetaA : Γ(XA p M H hj A, XFinA p M H hj A) ≅ CommRingCat.of (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
  θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 _)

theorem thetaA_section (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    (thetaA p M H hj A).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app
      ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))) =
      (1 : ↥A) ⊗ₜ[R p] b := by
  have h := θ_section (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A)) b (K := ↥A)
  first | simpa only [Category.id_comp] using h | (simp only [Category.id_comp] at h; exact h) | exact h

theorem gChart_snd_A :
    gChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A)) ≫
      pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))) =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) := by
  have := gChart_comp_snd (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A)) (K := ↥A)
  simpa using this

theorem thetaA_const (a : ↥A) :
    (thetaA p M H hj A).hom ((XA p M H hj A).presheaf.map (homOfLE le_top).op
      ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) = a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj)) :=
  θ_const (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 _)
    (pullback.snd _ _) (gChart_snd_A p M H hj A) a

end ChartA

namespace GaussStalkLift

noncomputable def reader {X G : Scheme.{0}} [IsIntegral G] (g : G ⟶ X) {T : Type} [CommRing T]
    (e : G.functionField →+* T) (O : X.Opens) [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O))] : Γ(X, O) →+* T :=
  e.comp ((G.germToFunctionField (g ⁻¹ᵁ O)).hom.comp (g.app O).hom)

theorem reader_apply {X G : Scheme.{0}} [IsIntegral G] (g : G ⟶ X) {T : Type} [CommRing T]
    (e : G.functionField →+* T) (O : X.Opens) [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O))] (s : Γ(X, O)) :
    reader g e O s = e (G.germToFunctionField (g ⁻¹ᵁ O) ((g.app O).hom s)) := rfl

theorem reader_res {X G : Scheme.{0}} [IsIntegral G] (g : G ⟶ X) {T : Type} [CommRing T]
    (e : G.functionField →+* T) (O O' : X.Opens) (h : O' ≤ O)
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O))] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O'))] (s : Γ(X, O)) :
    reader g e O' ((X.presheaf.map (homOfLE h).op).hom s) = reader g e O s := by
  simp only [reader_apply]
  congr 1
  have h1 : (g.app O').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (G.presheaf.map (homOfLE (show g ⁻¹ᵁ O' ≤ g ⁻¹ᵁ O from fun x hx => h hx)).op).hom ((g.app O).hom s) := by
    have h2 := congrArg (fun φ => φ.hom s) (g.naturality (homOfLE h).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    exact h2
  rw [h1]
  exact TopCat.Presheaf.germ_res_apply G.presheaf _ _ _ _

theorem germToFunctionField_app_app_of_comp_eq {M X Y : Scheme.{0}} [IrreducibleSpace M]
    (t : M ⟶ X) (F : X ⟶ Y) (φ : M ⟶ Y) (h : t ≫ F = φ) (O : Y.Opens)
    [Nonempty (Scheme.Opens.toScheme (t ⁻¹ᵁ (F ⁻¹ᵁ O)))] [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ O))]
    (x : Γ(Y, O)) :
    M.germToFunctionField (t ⁻¹ᵁ (F ⁻¹ᵁ O)) ((t.app (F ⁻¹ᵁ O)).hom ((F.app O).hom x)) =
      M.germToFunctionField (φ ⁻¹ᵁ O) ((φ.app O).hom x) := by
  subst h
  rfl

namespace ScalarReadAux

theorem germ_top_appTop_congr {Y X : Scheme.{0}} [IsIntegral Y] {φ ψ : Y ⟶ X} (h : φ = ψ) (x : Γ(X, ⊤)) :
    (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (φ.appTop.hom x) =
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (ψ.appTop.hom x) := by
  subst h
  rfl

theorem germToFunctionField_preimage_top_eq {Y X : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X)
    [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ⊤))] (x : Γ(X, ⊤)) :
    Y.germToFunctionField (φ ⁻¹ᵁ ⊤) ((φ.app ⊤).hom x) = (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (φ.appTop.hom x) := by
  rfl

theorem germToFunctionField_app_appTop_eq_germ_comp_appTop {Y X Z : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X) (χ : X ⟶ Z)
    [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ⊤))] (x : Γ(Z, ⊤)) :
    Y.germToFunctionField (φ ⁻¹ᵁ ⊤) ((φ.app ⊤).hom (χ.appTop.hom x)) =
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom ((φ ≫ χ).appTop.hom x) := by
  rfl

theorem germToFunctionField_app_appTop_eq_of_comp_eq {Y X S : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X) (snd : X ⟶ S) (ψ : Y ⟶ S)
    (hc : φ ≫ snd = ψ) [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ⊤))] (x : Γ(S, ⊤)) :
    Y.germToFunctionField (φ ⁻¹ᵁ ⊤) ((φ.app ⊤).hom (snd.appTop.hom x)) =
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (ψ.appTop.hom x) := by
  subst hc
  rfl

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := by
  rfl

theorem appTop_specMap_ΓSpecIso_inv {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (f r) := by
  have h := congrArg (fun g : CommRingCat.of R ⟶ _ => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h.symm

end ScalarReadAux

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_fst_iotaFin_eq_coeffEmb
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))))]
    (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
  haveI := 𝔛.Meta_chart_nonempty
  refine Eq.trans ?_ (𝔛.Meta_pin b)
  exact congrArg (fun z => ((𝔛.Meta.ffEquiv.symm z : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    (germToFunctionField_app_app_of_comp_eq gA (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) _ hgA₁ _ _)

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_snd_eq_coeffMap_C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ⊤))]
    (a : ↥Pl) :
    ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ⊤)
        ((gA.app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap Pl.subtype (HahnSeries.C a) := by

  have h1 : 𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ⊤)
      ((gA.app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
      (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
        ((𝔛.Meta.toBase ≫ barPt Pl).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) := by
    exact ScalarReadAux.germToFunctionField_app_appTop_eq_of_comp_eq gA _ _ hgA₂ _

  have h2 : (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
        ((𝔛.Meta.toBase ≫ barPt Pl).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) =
      AlgebraicCurve.baseToFunctionField 𝔛.Meta.toBase (a : AlgebraicClosure ℚ) := by
    rw [ScalarReadAux.appTop_comp_apply, show (barPt Pl).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (a : AlgebraicClosure ℚ) from
      ScalarReadAux.appTop_specMap_ΓSpecIso_inv Pl.subtype a]
    rfl
  rw [h1, h2, show 𝔛.Meta.ffEquiv.symm (AlgebraicCurve.baseToFunctionField 𝔛.Meta.toBase (a : AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) from
    (RingEquiv.symm_apply_eq _).mpr (𝔛.Meta.ffEquiv_algebraMap _).symm]
  show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) = _
  rw [HahnSeries.C_apply, coeffMap_single, ModularCurve.algebraMap_laurentSeries_eq_single]
  rfl

end GaussStalkLift

section ReadGamma

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
  (gA : 𝔛.Meta.C ⟶ XA p M H hj A)
  (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
  (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)

include hgA₁ in
theorem nonempty_gA_preimage_XFinA : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (XFinA p M H hj A))) := by
  show Nonempty (Scheme.Opens.toScheme ((gA ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))
  rw [hgA₁]
  exact 𝔛.Meta_chart_nonempty

theorem nonempty_gA_preimage_top : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ (⊤ : (XA p M H hj A).Opens))) :=
  ⟨⟨genericPoint 𝔛.Meta.C, trivial⟩⟩

include hρ hgA₁ hgA₂ hA in
set_option maxHeartbeats 3200000 in

theorem read_thetaA_inv_eq
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (t : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :
    haveI := nonempty_gA_preimage_XFinA p M H hpM hj 𝔛 A gA hgA₁
    GaussStalkLift.reader gA 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) ((thetaA p M H hj A).inv t) = γ t := by
  haveI := nonempty_gA_preimage_XFinA p M H hpM hj 𝔛 A gA hgA₁
  haveI := nonempty_gA_preimage_top p M H hpM hj 𝔛 A gA

  let Φ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H) :=
    (GaussStalkLift.reader gA 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A)).comp (thetaA p M H hj A).inv.hom
  have hΦ : ∀ x, Φ x = GaussStalkLift.reader gA 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) ((thetaA p M H hj A).inv x) :=
    fun x => rfl
  have hone : ∀ b : ↥(chartAlgFin p (ΓM M H) hj), Φ ((1 : ↥A) ⊗ₜ[R p] b) = γ ((1 : ↥A) ⊗ₜ b) := by
    intro b
    have hsec : (thetaA p M H hj A).inv ((1 : ↥A) ⊗ₜ[R p] b) =
        ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
          (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b)) := by
      rw [← thetaA_section p M H hj A b, Iso.hom_inv_id_apply]
    rw [hΦ, hsec]
    apply Subtype.ext
    rw [hγ, OneMemClass.coe_one, one_smul]
    exact GaussStalkLift.ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_fst_iotaFin_eq_coeffEmb p M hpM H A hA hj 𝔛
      (algebraMap (R p) ↥A) hρ gA hgA₁ b
  have hconst : ∀ a : ↥A, Φ (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) = γ (a ⊗ₜ 1) := by
    intro a
    have hsec : (thetaA p M H hj A).inv (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) =
        ((XA p M H hj A).presheaf.map (homOfLE le_top).op).hom
          ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) := by
      rw [← thetaA_const p M H hj A a, Iso.hom_inv_id_apply]
    rw [hΦ, hsec, GaussStalkLift.reader_res gA _ ⊤ (XFinA p M H hj A) le_top]
    apply Subtype.ext
    rw [hγ, OneMemClass.coe_one, OneMemClass.coe_one, map_one, ← HahnSeries.C_mul_eq_smul, mul_one]
    refine (GaussStalkLift.ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_snd_eq_coeffMap_C p M hpM H A hA hj 𝔛
      (algebraMap (R p) ↥A) hρ gA hgA₁ hgA₂ a).trans ?_
    rw [HahnSeries.C_apply, coeffMap_single, HahnSeries.C_apply]
    rfl

  show Φ t = γ t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
      have : a ⊗ₜ[R p] b = (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) * ((1 : ↥A) ⊗ₜ[R p] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, map_mul, hconst, hone]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end ReadGamma

end BranchReadSkel
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

namespace BranchReadE

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Algebra

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simpa only [coeffMap_coeff] using this

theorem eq_of_presentations {A K κ : Type*} [CommRing A] [Field K] [Field κ]
    (ι : A →+* K) (hι : Function.Injective ι) (red : A →+* κ)
    (h : LaurentSeries K) (x y xs ys : LaurentSeries A)
    (hy : coeffMap red y ≠ 0) (hys : coeffMap red ys ≠ 0)
    (h1 : h * coeffMap ι y = coeffMap ι x) (h2 : h * coeffMap ι ys = coeffMap ι xs)
    (g r : LaurentSeries κ)
    (hg : g * coeffMap red y = coeffMap red x) (hr : r * coeffMap red ys = coeffMap red xs) :
    g = r := by
  have hxy : x * ys = xs * y := by
    apply coeffMap_injective ι hι
    rw [map_mul, map_mul, ← h1, ← h2]; ring
  have hbar : coeffMap red x * coeffMap red ys = coeffMap red xs * coeffMap red y := by
    rw [← map_mul, hxy, map_mul]
  have key : g * (coeffMap red y * coeffMap red ys) = r * (coeffMap red y * coeffMap red ys) := by
    calc g * (coeffMap red y * coeffMap red ys) = (g * coeffMap red y) * coeffMap red ys := by ring
      _ = coeffMap red x * coeffMap red ys := by rw [hg]
      _ = coeffMap red xs * coeffMap red y := hbar
      _ = (r * coeffMap red ys) * coeffMap red y := by rw [hr]
      _ = r * (coeffMap red y * coeffMap red ys) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hy hys) key

end Algebra
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

section Maps

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) {hpM : p ∣ M}
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

def gA (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ)) : 𝔛.Meta.C ⟶ XA p M H hj A :=
  pullback.lift (𝔛.eeta ≫ pullback.fst _ _) (𝔛.Meta.toBase ≫ barPt A) (by
    have h1 : 𝔛.eeta ≫ pullback.snd _ _ = 𝔛.Meta.toBase := 𝔛.heeta
    simp only [Category.assoc, pullback.condition]
    rw [reassoc_of% h1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])

@[reassoc]
theorem gA_fst (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ)) :
    gA p M H hj 𝔛 A hρ ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc]
theorem gA_snd (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ)) :
    gA p M H hj 𝔛 A hρ ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A := pullback.lift_snd _ _ _

def bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)) ⟶ XA p M H hj A :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

@[reassoc]
theorem bc_fst : bc p M H hj A ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc]
theorem bc_snd : bc p M H hj A ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) :=
  pullback.lift_snd _ _ _

def wA : XA p M H hj A ⟶ XA p M H hj A :=
  pullback.map _ _ _ _ 𝔛.w.hom (𝟙 _) (𝟙 _) (by rw [𝔛.w_over, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem wA_fst : wA p M H hj 𝔛 A ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.hom := pullback.lift_fst _ _ _

@[reassoc]
theorem wA_snd : wA p M H hj 𝔛 A ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)

abbrev wbar : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)) ⟶
    fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)) :=
  fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))

omit [Fact p.Prime] [NeZero M] in
@[reassoc]
theorem fibreMap_fst {Γ Γ' : Subgroup SL(2, ℤ)} (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  delta XHDRLevel.fibreMap
  exact pullback.lift_fst _ _ _

omit [Fact p.Prime] [NeZero M] in
@[reassoc]
theorem fibreMap_snd {Γ Γ' : Subgroup SL(2, ℤ)} (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  delta XHDRLevel.fibreMap
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem bc_wA : bc p M H hj A ≫ wA p M H hj 𝔛 A = wbar p M H hj 𝔛 A ≫ bc p M H hj A := by
  apply pullback.hom_ext
  · rw [Category.assoc, wA_fst, bc_fst_assoc, Category.assoc, bc_fst, fibreMap_fst]; rfl
  · rw [Category.assoc, wA_snd, bc_snd, Category.assoc, bc_snd, fibreMap_snd_assoc]

end Maps
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

section Points

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

include 𝔛 in
theorem lft_fibre_snd {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    LocallyOfFiniteType (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) := by
  haveI := 𝔛.lfp
  infer_instance

include 𝔛 in

theorem section_ext {z z' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))}
    (hz : z ≫ pullback.snd _ _ = 𝟙 _) (hz' : z' ≫ pullback.snd _ _ = 𝟙 _)
    (h : z.base (closedPoint (ResidueField ↥A)) = z'.base (closedPoint (ResidueField ↥A))) : z = z' := by
  haveI := lft_fibre_snd (hj := hj) 𝔛 ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))
  exact ext_of_apply_closedPoint_eq (pullback.snd _ _) hz hz' h

def P0 (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1))) :
    closedPoints (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C :=
  ⟨(inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n), (𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n).2.choose⟩

def P1 (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1))) :
    closedPoints (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C :=
  ⟨(inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n), (𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n).1.choose⟩

theorem placeOfPoint_P0 (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1))) :
    (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).placeOfPoint (P0 𝔛 A hA hρ n) = 𝔛.placeOn0 A hA (algebraMap (R p) ↥A) hρ n :=
  (𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n).2.choose_spec

theorem placeOfPoint_P1 (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1))) :
    (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).placeOfPoint (P1 𝔛 A hA hρ n) = 𝔛.placeOn1 A hA (algebraMap (R p) ↥A) hρ n :=
  (𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n).1.choose_spec

def zOf (P : closedPoints (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) :
    {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C // q ≫ (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase = 𝟙 _} :=
  (pointEquivClosedPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase).symm P

theorem pointEquivPlace_zOf (P : closedPoints (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) :
    (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).pointEquivPlace (zOf 𝔛 A hA hρ P) = (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).placeOfPoint P := by
  rw [CurveModel.pointEquivPlace_apply, zOf, Equiv.apply_symm_apply]

theorem zOf_base (P : closedPoints (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) :
    (zOf 𝔛 A hA hρ P).1.base (closedPoint (ResidueField ↥A)) = P.1 := by
  simp [zOf]

theorem zOf_efib_comp_snd (P : closedPoints (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) (i : Fin 2) :
    ((zOf 𝔛 A hA hρ P).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ i) ≫ pullback.snd _ _ = 𝟙 _ := by
  rw [Category.assoc, Category.assoc, 𝔛.comp_over, 𝔛.hefib]
  exact (zOf 𝔛 A hA hρ P).2

theorem inv_efib_efib_base (x : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))) :
    (𝔛.efib A hA (algebraMap (R p) ↥A) hρ).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl

theorem zOf_P0_comp0_eq (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))
    (ht2 : t ≫ pullback.snd _ _ = 𝟙 _)
    (ht3 : t.base (closedPoint (ResidueField ↥A)) =
      (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base n) :
    (zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 = t := by
  apply section_ext 𝔛 A (zOf_efib_comp_snd 𝔛 A hA hρ (P0 𝔛 A hA hρ n) 0) ht2
  rw [ht3, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, zOf_base, P0, inv_efib_efib_base]
  rfl

theorem zOf_P1_comp1_eq (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))
    (ht2 : t ≫ pullback.snd _ _ = 𝟙 _)
    (ht3 : t.base (closedPoint (ResidueField ↥A)) =
      (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base n) :
    (zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1 = t := by
  apply section_ext 𝔛 A (zOf_efib_comp_snd 𝔛 A hA hρ (P1 𝔛 A hA hρ n) 1) ht2
  rw [ht3, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, zOf_base, P1, inv_efib_efib_base, Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply _ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1), ← pullback.condition]
  rfl

theorem zOf_P1_comp0_wbar_eq (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))
    (ht2 : t ≫ pullback.snd _ _ = 𝟙 _)
    (ht3 : t.base (closedPoint (ResidueField ↥A)) =
      (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base n) :
    (zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ wbar p M H hj 𝔛 A = t := by
  rw [← zOf_P1_comp1_eq 𝔛 A hA hρ n t ht2 ht3, ← 𝔛.comp_w A hA (algebraMap (R p) ↥A) hρ]

end Points
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

section Chart

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

abbrev gChartA : Spec (CommRingCat.of (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ XA p M H hj A :=
  gChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A))

omit [Fact p.Prime] [NeZero M] in
theorem gChartA_fst : gChartA p M H hj A ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
      ιFin p (ΓM M H) hj := by
  have h := gChart_comp_fst (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A)) (K := ↥A)
  first | simpa only [Category.id_comp] using h | (simp only [Category.id_comp] at h; exact h) | exact h

omit [Fact p.Prime] [NeZero M] in
theorem top_le_gChartA_preimage_XFinA : ⊤ ≤ (gChartA p M H hj A) ⁻¹ᵁ XFinA p M H hj A :=
  top_le_preimage_U (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A))

omit [Fact p.Prime] [NeZero M] in
theorem thetaA_hom_apply (s : Γ(XA p M H hj A, XFinA p M H hj A)) :
    (thetaA p M H hj A).hom.hom s = (Scheme.ΓSpecIso (CommRingCat.of (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))).hom.hom
      (((gChartA p M H hj A).appLE (XFinA p M H hj A) ⊤ (top_le_gChartA_preimage_XFinA p M H hj A)).hom s) := rfl

def Dc (c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) : (XA p M H hj A).Opens :=
  (XA p M H hj A).basicOpen ((thetaA p M H hj A).inv c)

omit [Fact p.Prime] [NeZero M] in
theorem Dc_le (c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) : Dc p M H hj A c ≤ XFinA p M H hj A :=
  (XA p M H hj A).basicOpen_le _

theorem gChartA_mem_Dc_iff (c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (𝔮 : ↥(Spec (CommRingCat.of (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))))) :
    (gChartA p M H hj A).base 𝔮 ∈ Dc p M H hj A c ↔ c ∉ 𝔮.asIdeal := by
  have h1 : (gChartA p M H hj A).base 𝔮 =
      (isAffineOpen_XFinA p M H hj A).fromSpec.base ((Spec.map (thetaA p M H hj A).hom).base 𝔮) :=
    (fromSpec_specθ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A)) 𝔮).symm
  have h2 : (isAffineOpen_XFinA p M H hj A).fromSpec.base ((Spec.map (thetaA p M H hj A).hom).base 𝔮) ∈ Dc p M H hj A c ↔
      (Spec.map (thetaA p M H hj A).hom).base 𝔮 ∈ (isAffineOpen_XFinA p M H hj A).fromSpec ⁻¹ᵁ Dc p M H hj A c := Iff.rfl
  rw [h1, h2, Dc, IsAffineOpen.fromSpec_preimage_basicOpen]
  show (thetaA p M H hj A).inv c ∉ Ideal.comap (thetaA p M H hj A).hom.hom 𝔮.asIdeal ↔ _
  rw [Ideal.mem_comap]
  show ¬ ((thetaA p M H hj A).inv ≫ (thetaA p M H hj A).hom).hom c ∈ 𝔮.asIdeal ↔ _
  rw [Iso.inv_hom_id]
  rfl

omit [Fact p.Prime] [NeZero M] in
theorem isUnit_resDc (c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) : IsUnit (((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv c)) :=
  RingedSpace.isUnit_res_basicOpen _ ((thetaA p M H hj A).inv c)

def secFrac (a c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) : Γ(XA p M H hj A, Dc p M H hj A c) :=
  ((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv a) * (((isUnit_resDc p M H hj A c).unit⁻¹ : (Γ(XA p M H hj A, Dc p M H hj A c))ˣ) : Γ(XA p M H hj A, Dc p M H hj A c))

omit [Fact p.Prime] [NeZero M] in
theorem secFrac_mul (a c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :
    secFrac p M H hj A a c * ((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv c) = ((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv a) := by
  rw [secFrac, mul_assoc, IsUnit.val_inv_mul, mul_one]

omit [Fact p.Prime] [NeZero M] in

theorem map_secFrac {L : Type*} [Field L] (a c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (F : Γ(XA p M H hj A, Dc p M H hj A c) →+* L) :
    F (secFrac p M H hj A a c) = F (((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv a)) * (F (((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv c)))⁻¹ := by
  have hu : F (((XA p M H hj A).presheaf.map (homOfLE (Dc_le p M H hj A c)).op).hom ((thetaA p M H hj A).inv c)) ≠ 0 := ((isUnit_resDc p M H hj A c).map F).ne_zero
  rw [eq_mul_inv_iff_mul_eq₀ hu, ← map_mul, secFrac_mul]

def ev {κ : Type} [CommRing κ] {Y : Scheme.{0}} (ζ : Spec (CommRingCat.of κ) ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ ζ ⁻¹ᵁ U) :
    Γ(Y, U) →+* κ :=
  (Scheme.ΓSpecIso (CommRingCat.of κ)).hom.hom.comp (ζ.appLE U ⊤ hU).hom

theorem ev_apply {κ : Type} [CommRing κ] {Y : Scheme.{0}} (ζ : Spec (CommRingCat.of κ) ⟶ Y) (U : Y.Opens) (hU : ⊤ ≤ ζ ⁻¹ᵁ U) (s : Γ(Y, U)) :
    ev ζ U hU s = (Scheme.ΓSpecIso (CommRingCat.of κ)).hom.hom ((ζ.appLE U ⊤ hU).hom s) := rfl

theorem ev_res {κ : Type} [CommRing κ] {Y : Scheme.{0}} (ζ : Spec (CommRingCat.of κ) ⟶ Y) (U U' : Y.Opens) (h : U' ≤ U)
    (hU : ⊤ ≤ ζ ⁻¹ᵁ U) (hU' : ⊤ ≤ ζ ⁻¹ᵁ U') (s : Γ(Y, U)) :
    ev ζ U' hU' ((Y.presheaf.map (homOfLE h).op).hom s) = ev ζ U hU s := by
  show (Scheme.ΓSpecIso _).hom.hom ((Y.presheaf.map (homOfLE h).op ≫ ζ.appLE U' ⊤ hU').hom s) =
    (Scheme.ΓSpecIso _).hom.hom ((ζ.appLE U ⊤ hU).hom s)
  rw [Scheme.Hom.map_appLE]

theorem ev_comp {κ : Type} [CommRing κ] {Y Z : Scheme.{0}} (ζ : Spec (CommRingCat.of κ) ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ ζ ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : Γ(Z, U)) :
    ev ζ (g ⁻¹ᵁ U) h ((g.app U).hom s) = ev (ζ ≫ g) U h s := by
  show (Scheme.ΓSpecIso _).hom.hom ((g.app U ≫ ζ.appLE (g ⁻¹ᵁ U) ⊤ h).hom s) = _
  rw [← Scheme.Hom.comp_appLE]
  rfl

theorem ev_congr {κ : Type} [CommRing κ] {Y : Scheme.{0}} {ζ ζ' : Spec (CommRingCat.of κ) ⟶ Y} (e : ζ = ζ') (U : Y.Opens)
    (h : ⊤ ≤ ζ ⁻¹ᵁ U) (h' : ⊤ ≤ ζ' ⁻¹ᵁ U) (s : Γ(Y, U)) : ev ζ U h s = ev ζ' U h' s := by
  subst e; rfl

theorem top_le_preimage_of_mem {κ : Type} [Field κ] {Y : Scheme.{0}} (ζ : Spec (CommRingCat.of κ) ⟶ Y) (U : Y.Opens)
    (h : ζ.base (closedPoint κ) ∈ U) : ⊤ ≤ ζ ⁻¹ᵁ U := by
  intro x _
  have hx : x = closedPoint κ := Subsingleton.elim _ _
  rw [hx]
  exact h

theorem mem_of_top_le_preimage {κ : Type} [Field κ] {Y : Scheme.{0}} (ζ : Spec (CommRingCat.of κ) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ ζ ⁻¹ᵁ U) : ζ.base (closedPoint κ) ∈ U :=
  h (Set.mem_univ (closedPoint κ))

theorem ev_specMap_comp {κ B : Type} [CommRing κ] [CommRing B] {Y : Scheme.{0}} (g : Spec (CommRingCat.of B) ⟶ Y) (χ : B →+* κ)
    (U : Y.Opens) (hU : ⊤ ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom χ) ≫ g) ⁻¹ᵁ U) (s : Γ(Y, U)) :
    ev (Spec.map (CommRingCat.ofHom χ) ≫ g) U h s = χ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((g.appLE U ⊤ hU).hom s)) := by
  have k1 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom χ)) g U ⊤ ⊤ hU le_top
  rw [appLE_top_top] at k1
  have k2 := congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of κ)).hom.hom (φ.hom s)) k1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at k2
  have k3 := congrArg (fun φ => φ.hom ((g.appLE U ⊤ hU).hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at k3
  rw [ev_apply]
  exact k2.symm.trans k3

omit [Fact p.Prime] [NeZero M] in

theorem ev_specMap_gChartA {κ : Type} [CommRing κ] (χ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* κ)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom χ) ≫ gChartA p M H hj A) ⁻¹ᵁ XFinA p M H hj A) (s : Γ(XA p M H hj A, XFinA p M H hj A)) :
    ev (Spec.map (CommRingCat.ofHom χ) ≫ gChartA p M H hj A) (XFinA p M H hj A) h s = χ ((thetaA p M H hj A).hom.hom s) := by
  rw [thetaA_hom_apply]
  exact ev_specMap_comp (gChartA p M H hj A) χ (XFinA p M H hj A) (top_le_gChartA_preimage_XFinA p M H hj A) h s

theorem specMap_gChartA_mem_Dc {κ : Type} [Field κ] (χ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* κ)
    (c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (hc : χ c ≠ 0) :
    (Spec.map (CommRingCat.ofHom χ) ≫ gChartA p M H hj A).base (closedPoint κ) ∈ Dc p M H hj A c := by
  rw [Scheme.Hom.comp_apply, gChartA_mem_Dc_iff]
  show χ c ∉ IsLocalRing.maximalIdeal κ
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  exact isUnit_iff_ne_zero.mpr hc

omit [Fact p.Prime] [NeZero M] in

theorem ev_secFrac {κ : Type} [Field κ] (χ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* κ)
    (a c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom χ) ≫ gChartA p M H hj A) ⁻¹ᵁ Dc p M H hj A c) :
    ev (Spec.map (CommRingCat.ofHom χ) ≫ gChartA p M H hj A) (Dc p M H hj A c) h (secFrac p M H hj A a c) = χ a / χ c := by
  have hX : ⊤ ≤ (Spec.map (CommRingCat.ofHom χ) ≫ gChartA p M H hj A) ⁻¹ᵁ XFinA p M H hj A := fun x hx => Dc_le p M H hj A c (h hx)
  rw [map_secFrac, ev_res _ _ _ (Dc_le p M H hj A c) hX h, ev_res _ _ _ (Dc_le p M H hj A c) hX h, ev_specMap_gChartA, ev_specMap_gChartA,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, CommRingCat.id_apply, div_eq_mul_inv]

end Chart
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

theorem hasValue_of_mem_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (g : F) (a : K)
    (hg : g ∈ v.toValuationSubring) (hsub : g - algebraMap K F a ∈ v.toValuationSubring.nonunits) : v.HasValue g a := by
  refine ⟨hg, ?_⟩
  have hd : (⟨g, hg⟩ : ↥v.toValuationSubring) - algebraMap K (↥v.toValuationSubring) a ∈ IsLocalRing.maximalIdeal ↥v.toValuationSubring := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact hsub
  have h2 : IsLocalRing.residue (↥v.toValuationSubring) (algebraMap K (↥v.toValuationSubring) a) = algebraMap K v.ResidueField a :=
    (Place.hasValue_algebraMap v a).residue_eq
  rw [← h2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hd

section E0

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
  (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
  (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
  (t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))
  (ht1 : t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj)
  (ht2 : t ≫ pullback.snd _ _ = 𝟙 _)

include ht1 ht2 hχA in
omit hpM 𝔛 hA [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] hρ in

theorem t_bc_eq : t ≫ bc p M H hj A = Spec.map (CommRingCat.ofHom χκ) ≫ gChartA p M H hj A := by
  apply pullback.hom_ext
  · rw [Category.assoc, bc_fst, ht1, Category.assoc, gChartA_fst]
  · rw [Category.assoc, bc_snd, reassoc_of% ht2, Category.assoc, gChart_snd_A, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hχA]

include ht1 ht2 hχA in
set_option maxHeartbeats 3200000 in

theorem hasValue_comp0 (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (ht3 : t.base (closedPoint (ResidueField ↥A)) =
      (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base n)
    (h : ↥(xHFunctionFieldBar M H)) (a c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (hc : χκ c ≠ 0) (hγc : γ c ≠ 0) (hhc : h * γ c = γ a)
    (x y : LaurentSeries ↥A) (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hg : (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x) :
    (𝔛.placeOn0 A hA (algebraMap (R p) ↥A) hρ n).HasValue g (χκ a / χκ c) := by
  classical
  have hzpt := zOf_P0_comp0_eq 𝔛 A hA hρ n t ht2 ht3
  have htbc := t_bc_eq p M H hj A χκ hχA t ht1 ht2
  have hchain : (zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A =
      Spec.map (CommRingCat.ofHom χκ) ≫ gChartA p M H hj A := by
    rw [← htbc, ← hzpt, Category.assoc, Category.assoc]

  have hpt : (bc p M H hj A).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base (P0 𝔛 A hA hρ n).1) =
      (Spec.map (CommRingCat.ofHom χκ) ≫ gChartA p M H hj A).base (closedPoint (ResidueField ↥A)) := by
    rw [← hchain, ← zOf_base 𝔛 A hA hρ (P0 𝔛 A hA hρ n)]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have hzU : (bc p M H hj A).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base (P0 𝔛 A hA hρ n).1) ∈
      Dc p M H hj A c := by
    rw [hpt]; exact specMap_gChartA_mem_Dc p M H hj A χκ c hc

  have hne : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ Dc p M H hj A c)) :=
    (ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 (algebraMap (R p) ↥A) hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ)).2.1 _ ⟨⟨_, hzU⟩⟩
  haveI := hne
  haveI := nonempty_gA_preimage_XFinA p M H hpM hj 𝔛 A (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ)

  obtain ⟨hneT, xs, ys, hys, hf, hr, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
      p M hpM hpM2 H hHp A hA hj 𝔛 (algebraMap (R p) ↥A) hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ)
      (bc p M H hj A) (bc_fst p M H hj A) (bc_snd p M H hj A) (P0 𝔛 A hA hρ n) (Dc p M H hj A c) hzU hne (secFrac p M H hj A a c)

  have hread : 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ Dc p M H hj A c)
      (((gA p M H hj 𝔛 A hρ).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c))) = h := by
    show GaussStalkLift.reader (gA p M H hj 𝔛 A hρ) 𝔛.Meta.ffEquiv.symm.toRingHom (Dc p M H hj A c) (secFrac p M H hj A a c) = h
    rw [map_secFrac, GaussStalkLift.reader_res (gA p M H hj 𝔛 A hρ) _ (XFinA p M H hj A) (Dc p M H hj A c) (Dc_le p M H hj A c),
      GaussStalkLift.reader_res (gA p M H hj 𝔛 A hρ) _ (XFinA p M H hj A) (Dc p M H hj A c) (Dc_le p M H hj A c),
      read_thetaA_inv_eq p M H hpM hj 𝔛 A hA hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ) γ hγ a,
      read_thetaA_inv_eq p M H hpM hj 𝔛 A hA hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ) γ hγ c]
    symm
    rw [eq_mul_inv_iff_mul_eq₀ hγc]
    exact hhc
  rw [hread] at hf

  have hgr := eq_of_presentations A.subtype Subtype.val_injective (IsLocalRing.residue ↥A)
    ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) x y xs ys hy hys hxy hf _ _ hg hr

  haveI := hneT
  have hz : ⊤ ≤ (zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)).1 ⁻¹ᵁ
      ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A) ⁻¹ᵁ Dc p M H hj A c) := by
    apply top_le_preimage_of_mem
    show ((zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).base
      (closedPoint (ResidueField ↥A)) ∈ Dc p M H hj A c
    rw [hchain]
    exact specMap_gChartA_mem_Dc p M H hj A χκ c hc
  obtain ⟨hmem, hsub⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
      (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ)
      ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A) ⁻¹ᵁ Dc p M H hj A c)
      (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c))
      (zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)) hz
  have hval : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField ↥A))).hom ((zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)).1.appLE _ ⊤ hz
      ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c)))) =
      χκ a / χκ c := by
    show ev (zOf 𝔛 A hA hρ (P0 𝔛 A hA hρ n)).1 _ hz
      ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c))) = _
    rw [ev_comp, ev_congr hchain (Dc p M H hj A c) hz (top_le_preimage_of_mem _ _ (specMap_gChartA_mem_Dc p M H hj A χκ c hc)), ev_secFrac]
  rw [hval] at hsub
  have hv := hasValue_of_mem_of_sub_mem_nonunits _ _ _ hmem hsub
  rw [pointEquivPlace_zOf, placeOfPoint_P0] at hv
  rwa [Subtype.ext hgr]

end E0
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

section Transport

open BranchReadSkel.GaussStalkLift

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

theorem germ_app_congr {Y X : Scheme.{0}} [IsIntegral Y] {φ ψ : Y ⟶ X} (h : φ = ψ) (O : X.Opens)
    [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ O))] [Nonempty (Scheme.Opens.toScheme (ψ ⁻¹ᵁ O))] (x : Γ(X, O)) :
    Y.germToFunctionField (φ ⁻¹ᵁ O) ((φ.app O).hom x) = Y.germToFunctionField (ψ ⁻¹ᵁ O) ((ψ.app O).hom x) := by
  subst h; rfl

include hρ in

theorem reader_top_snd_const (G : 𝔛.Meta.C ⟶ XA p M H hj A) (hG : G ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    [Nonempty (Scheme.Opens.toScheme (G ⁻¹ᵁ (⊤ : (XA p M H hj A).Opens)))] (a : ↥A) :
    reader G 𝔛.Meta.ffEquiv.symm.toRingHom ⊤
      ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by
  rw [reader_apply]
  have h1 : 𝔛.Meta.C.germToFunctionField (G ⁻¹ᵁ ⊤)
      ((G.app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
      (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
        ((𝔛.Meta.toBase ≫ barPt A).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) :=
    ScalarReadAux.germToFunctionField_app_appTop_eq_of_comp_eq G _ _ hG _
  have h2 : (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
        ((𝔛.Meta.toBase ≫ barPt A).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) =
      AlgebraicCurve.baseToFunctionField 𝔛.Meta.toBase (a : AlgebraicClosure ℚ) := by
    rw [ScalarReadAux.appTop_comp_apply, show (barPt A).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (a : AlgebraicClosure ℚ) from
      ScalarReadAux.appTop_specMap_ΓSpecIso_inv A.subtype a]
    rfl
  show 𝔛.Meta.ffEquiv.symm _ = _
  rw [h1, h2]
  exact (RingEquiv.symm_apply_eq _).mpr (𝔛.Meta.ffEquiv_algebraMap _).symm

theorem reader_comp_wA_eq (U : (XA p M H hj A).Opens)
    (i1 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ⁻¹ᵁ U)))
    (i2 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ ((wA p M H hj 𝔛 A) ⁻¹ᵁ U)))) (y : Γ(XA p M H hj A, U)) :
    @reader _ _ _ (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) _ _ 𝔛.Meta.ffEquiv.symm.toRingHom U i1 y =
      @reader _ _ _ (gA p M H hj 𝔛 A hρ) _ _ 𝔛.Meta.ffEquiv.symm.toRingHom ((wA p M H hj 𝔛 A) ⁻¹ᵁ U) i2 (((wA p M H hj 𝔛 A).app U).hom y) := rfl

set_option maxHeartbeats 3200000 in

theorem theta_reader_eq
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (i1 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ XFinA p M H hj A)))
    (i3 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ⁻¹ᵁ XFinA p M H hj A)))
    (s : Γ(XA p M H hj A, XFinA p M H hj A)) :
    θ (@reader _ _ _ (gA p M H hj 𝔛 A hρ) _ _ 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) i1 s) =
      @reader _ _ _ (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) _ _ 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) i3 s := by
  classical
  haveI := i1
  haveI := i3
  haveI i4 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ (⊤ : (XA p M H hj A).Opens))) := ⟨⟨genericPoint 𝔛.Meta.C, trivial⟩⟩
  haveI i5 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ⁻¹ᵁ (⊤ : (XA p M H hj A).Opens))) :=
    ⟨⟨genericPoint 𝔛.Meta.C, trivial⟩⟩
  haveI iV : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
      ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := 𝔛.Meta_chart_nonempty
  have hcomp : (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ≫ pullback.fst _ _ =
      𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫ 𝔛.w.hom := by
    rw [Category.assoc, wA_fst, gA_fst_assoc]
  haveI iW : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫ 𝔛.w.hom) ⁻¹ᵁ
      ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := by
    rw [← hcomp]; exact i3
  haveI iW' : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
      (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))) := iW

  obtain ⟨t, rfl⟩ : ∃ t, s = (thetaA p M H hj A).inv t := ⟨(thetaA p M H hj A).hom s, by rw [Iso.hom_inv_id_apply]⟩

  have hone : ∀ b : ↥(chartAlgFin p (ΓM M H) hj),
      θ (reader (gA p M H hj 𝔛 A hρ) 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) ((thetaA p M H hj A).inv ((1 : ↥A) ⊗ₜ[R p] b))) =
        reader (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) ((thetaA p M H hj A).inv ((1 : ↥A) ⊗ₜ[R p] b)) := by
    intro b
    have hsec : (thetaA p M H hj A).inv ((1 : ↥A) ⊗ₜ[R p] b) =
        ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
          (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b)) := by
      rw [← thetaA_section p M H hj A b, Iso.hom_inv_id_apply]
    rw [hsec, reader_apply, reader_apply]
    have hL := germToFunctionField_app_app_of_comp_eq (gA p M H hj 𝔛 A hρ)
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))))
      (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) (gA_fst p M H hj 𝔛 A hρ)
      ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))
    have hR := germToFunctionField_app_app_of_comp_eq (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A)
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))))
      (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫ 𝔛.w.hom) hcomp
      ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))
    have hR' := germToFunctionField_app_app_of_comp_eq
      (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) 𝔛.w.hom
      (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫ 𝔛.w.hom) (Category.assoc _ _ _)
      ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))
    have hW := ModularCurve.XHDRModelAtP.algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
      p M H hpM hj 𝔛 θ hwgen ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) iV iW' (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))
    show θ (𝔛.Meta.ffEquiv.symm _) = 𝔛.Meta.ffEquiv.symm _
    rw [hL, hR, ← hR']
    exact hW

  have hconst : ∀ a : ↥A,
      θ (reader (gA p M H hj 𝔛 A hρ) 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) ((thetaA p M H hj A).inv (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))))) =
        reader (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) 𝔛.Meta.ffEquiv.symm.toRingHom (XFinA p M H hj A) ((thetaA p M H hj A).inv (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj)))) := by
    intro a
    have hsec : (thetaA p M H hj A).inv (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) =
        ((XA p M H hj A).presheaf.map (homOfLE le_top).op).hom
          ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) := by
      rw [← thetaA_const p M H hj A a, Iso.hom_inv_id_apply]
    have hGw : (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A := by
      rw [Category.assoc, wA_snd, gA_snd]
    rw [hsec, reader_res (gA p M H hj 𝔛 A hρ) _ ⊤ (XFinA p M H hj A) le_top, reader_res (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) _ ⊤ (XFinA p M H hj A) le_top,
      reader_top_snd_const p M H hpM hj 𝔛 A hρ (gA p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ) a,
      reader_top_snd_const p M H hpM hj 𝔛 A hρ (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) hGw a, AlgEquiv.commutes]

  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a b =>
      have : a ⊗ₜ[R p] b = (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) * ((1 : ↥A) ⊗ₜ[R p] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      simp only [map_mul]
      rw [hconst, hone]
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

end Transport
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

section E1

open BranchReadSkel.GaussStalkLift

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
  (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
    y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
    𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
  (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
  (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
  (t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))
  (ht1 : t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj)
  (ht2 : t ≫ pullback.snd _ _ = 𝟙 _)

include ht1 ht2 hχA hwgen in
set_option maxHeartbeats 3200000 in

theorem hasValue_comp1 (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (ht3 : t.base (closedPoint (ResidueField ↥A)) =
      (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base n)
    (h : ↥(xHFunctionFieldBar M H)) (a c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (hc : χκ c ≠ 0) (hγc : γ c ≠ 0) (hhc : h * γ c = γ a)
    (x y : LaurentSeries ↥A) (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hg : (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x) :
    (𝔛.placeOn1 A hA (algebraMap (R p) ↥A) hρ n).HasValue g (χκ a / χκ c) := by
  classical
  have hzpt := zOf_P1_comp0_wbar_eq 𝔛 A hA hρ n t ht2 ht3
  have htbc := t_bc_eq p M H hj A χκ hχA t ht1 ht2
  have hchain : ((zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A) ≫
      wA p M H hj 𝔛 A = Spec.map (CommRingCat.ofHom χκ) ≫ gChartA p M H hj A := by
    rw [← htbc, ← hzpt]
    simp only [Category.assoc]
    rw [bc_wA]

  have hpt : (wA p M H hj 𝔛 A).base ((bc p M H hj A).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base (P1 𝔛 A hA hρ n).1)) =
      (Spec.map (CommRingCat.ofHom χκ) ≫ gChartA p M H hj A).base (closedPoint (ResidueField ↥A)) := by
    rw [← hchain, ← zOf_base 𝔛 A hA hρ (P1 𝔛 A hA hρ n)]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have hzU : (bc p M H hj A).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base (P1 𝔛 A hA hρ n).1) ∈
      (wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c := by
    show (wA p M H hj 𝔛 A).base _ ∈ Dc p M H hj A c
    rw [hpt]; exact specMap_gChartA_mem_Dc p M H hj A χκ c hc

  have hne : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c))) :=
    (ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 (algebraMap (R p) ↥A) hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ)).2.1 _ ⟨⟨_, hzU⟩⟩
  haveI := hne
  haveI i1 := nonempty_gA_preimage_XFinA p M H hpM hj 𝔛 A (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ)
  haveI i2 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)) := hne
  haveI i3 : Nonempty (Scheme.Opens.toScheme ((gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) ⁻¹ᵁ XFinA p M H hj A)) :=
    ⟨⟨i2.some.1, Dc_le p M H hj A c i2.some.2⟩⟩

  obtain ⟨hneT, xs, ys, hys, hf, hr, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
      p M hpM hpM2 H hHp A hA hj 𝔛 (algebraMap (R p) ↥A) hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ)
      (bc p M H hj A) (bc_fst p M H hj A) (bc_snd p M H hj A) (P1 𝔛 A hA hρ n) ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c) hzU hne
      (((wA p M H hj 𝔛 A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c))

  have hread : 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField ((gA p M H hj 𝔛 A hρ) ⁻¹ᵁ ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c))
      (((gA p M H hj 𝔛 A hρ).app ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)).hom (((wA p M H hj 𝔛 A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c)))) = θ h := by
    show reader (gA p M H hj 𝔛 A hρ) 𝔛.Meta.ffEquiv.symm.toRingHom ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)
      (((wA p M H hj 𝔛 A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c)) = θ h
    rw [← reader_comp_wA_eq p M H hpM hj 𝔛 A hρ (Dc p M H hj A c) i2 hne, map_secFrac,
      reader_res (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) _ (XFinA p M H hj A) (Dc p M H hj A c) (Dc_le p M H hj A c),
      reader_res (gA p M H hj 𝔛 A hρ ≫ wA p M H hj 𝔛 A) _ (XFinA p M H hj A) (Dc p M H hj A c) (Dc_le p M H hj A c),
      ← theta_reader_eq p M H hpM hj 𝔛 A hρ θ hwgen i1 i3, ← theta_reader_eq p M H hpM hj 𝔛 A hρ θ hwgen i1 i3,
      read_thetaA_inv_eq p M H hpM hj 𝔛 A hA hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ) γ hγ a,
      read_thetaA_inv_eq p M H hpM hj 𝔛 A hA hρ (gA p M H hj 𝔛 A hρ) (gA_fst p M H hj 𝔛 A hρ) (gA_snd p M H hj 𝔛 A hρ) γ hγ c,
      ← map_inv₀, ← map_mul]
    congr 1
    symm
    rw [eq_mul_inv_iff_mul_eq₀ hγc]
    exact hhc
  rw [hread] at hf

  have hgr := eq_of_presentations A.subtype Subtype.val_injective (IsLocalRing.residue ↥A)
    ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) x y xs ys hy hys hxy hf _ _ hg hr

  haveI := hneT
  have hz : ⊤ ≤ (zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1 ⁻¹ᵁ
      ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A) ⁻¹ᵁ ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)) := by
    apply top_le_preimage_of_mem
    show (((zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1 ≫ 𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A) ≫
      wA p M H hj 𝔛 A).base (closedPoint (ResidueField ↥A)) ∈ Dc p M H hj A c
    rw [hchain]
    exact specMap_gChartA_mem_Dc p M H hj A χκ c hc
  obtain ⟨hmem, hsub⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
      (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ)
      ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A) ⁻¹ᵁ ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c))
      (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).app ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)).hom
        (((wA p M H hj 𝔛 A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c)))
      (zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)) hz
  have hval : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField ↥A))).hom ((zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1.appLE _ ⊤ hz
      ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).app ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)).hom
        (((wA p M H hj 𝔛 A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c))))) =
      χκ a / χκ c := by
    show ev (zOf 𝔛 A hA hρ (P1 𝔛 A hA hρ n)).1 _ hz
      ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc p M H hj A).app ((wA p M H hj 𝔛 A) ⁻¹ᵁ Dc p M H hj A c)).hom
        (((wA p M H hj 𝔛 A).app (Dc p M H hj A c)).hom (secFrac p M H hj A a c)))) = _
    rw [ev_comp, ev_comp, ev_congr hchain (Dc p M H hj A c) hz (top_le_preimage_of_mem _ _ (specMap_gChartA_mem_Dc p M H hj A χκ c hc)), ev_secFrac]
  rw [hval] at hsub
  have hv := hasValue_of_mem_of_sub_mem_nonunits _ _ _ hmem hsub
  rw [pointEquivPlace_zOf, placeOfPoint_P1] at hv
  rwa [Subtype.ext hgr]

end E1
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

section Final

set_option maxHeartbeats 3200000 in

theorem value_clauses_core
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (hγinj : Function.Injective γ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)
    : ∀ (h : ↥(xHFunctionFieldBar M H)) (a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))), c ∉ 𝔔 → h * γ c = γ a →
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn0 A hA ρ hρ n).HasValue g (χκ a / χκ c)) ∧
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn1 A hA ρ hρ n).HasValue g (χκ a / χκ c)) := by
  subst halg
  obtain ⟨t, ht1, ht2, ht3⟩ := ht
  intro h a c hc𝔔 hhc
  have hc : χκ c ≠ 0 := fun h0 => hc𝔔 (hker ▸ (RingHom.mem_ker).mpr h0)
  have hγc : γ c ≠ 0 := fun h0 => hc𝔔 (((map_eq_zero_iff γ hγinj).mp h0).symm ▸ 𝔔.zero_mem)
  refine ⟨fun x y hy hxy g hg => ?_, fun x y hy hxy g hg => ?_⟩
  · exact hasValue_comp0 p M H hpM hj 𝔛 A hA hρ χκ hχA t ht1 ht2 hpM2 hHp γ hγ n ht3 h a c hc hγc hhc x y hy hxy g hg
  · exact hasValue_comp1 p M H hpM hj 𝔛 A hA hρ θ hwgen χκ hχA t ht1 ht2 hpM2 hHp γ hγ n ht3 h a c hc hγc hhc x y hy hxy g hg

end Final
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

end BranchReadE
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (hγinj : Function.Injective γ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)
    : ∀ (h : ↥(xHFunctionFieldBar M H)) (a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))), c ∉ 𝔔 → h * γ c = γ a →
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn0 A hA ρ hρ n).HasValue g (χκ a / χκ c)) ∧
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn1 A hA ρ hρ n).HasValue g (χκ a / χκ c)) :=
  BranchReadE.value_clauses_core p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg θ hwgen γ hγ hγinj n 𝔔 χκ hker hχA ht

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.BranchReadSkel"

end S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime (solution)
