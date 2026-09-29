-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2e546812-937e-52d7-8833-7d92314516a9

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
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
import Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

open scoped TensorProduct

noncomputable section

namespace BranchReadSkel

open ModularCurve AlgebraicCurve
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
  first | exact h | simpa only [Category.id_comp] using h | (simp only [Category.id_comp] at h; exact h) | (simp only [Category.id_comp]; exact h) | (simp only [Category.id_comp] at h ⊢; exact h)

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

theorem base_inv_base_apply {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (y : Y) : f.base ((inv f).base y) = y := by
  show ((inv f) ≫ f).base y = y
  rw [IsIso.inv_hom_id]; rfl

section S4

set_option maxHeartbeats 6400000 in
theorem theta_gamma_mem_integers
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :
    ∀ t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), θ (γ t) ∈ Rg.integers := by
  classical
  obtain ⟨⟨h₁mem, h₁pl⟩, -⟩ := 𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n
  obtain ⟨tκ, ht₁, -, ht₃⟩ := ht

  have hxfin : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) := by
    rw [← ht₃]
    show (tκ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    rw [ht₁, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩

  have hfib : XHDRLevel.fibreMap (XHDRLevel.overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) = (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) ≫ 𝔛.w.hom :=
    pullback.lift_fst _ _ _
  have hw : 𝔛.w.hom.base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) =
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n) := by
    have h1 := congrArg (fun φ => (φ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))
      (𝔛.comp_w A hA (algebraMap (R p) ↥A) hρ)
    have h3 := congrArg (fun φ => (φ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base n) (pullback.condition (f := (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)) (g := (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    simp only [Category.assoc] at h1
    rw [hfib] at h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1 h3 ⊢
    rw [h1, ← h3]

  have hP₁ : (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n)) =
      (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n) := by
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [base_inv_base_apply]
  have hzU : bc.base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) ∈
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) := by
    rw [hP₁]
    show 𝔛.w.hom.base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).base (bc.base _)) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    have hb := congrArg (fun φ => φ.base ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) hbc₁
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hb
    rw [hb, hw]
    exact hxfin

  haveI hU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := 𝔛.Meta_chart_nonempty
  have hneU : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))))) :=
    (ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 (algebraMap (R p) ↥A) hρ gA hgA₁ hgA₂).2.1 _ ⟨⟨_, hzU⟩⟩
  have hwU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))) := by
    rw [← hgA₁]; exact hneU

  have hb : ∀ b : ↥(chartAlgFin p (ΓM M H) hj), θ (γ ((1 : ↥A) ⊗ₜ[R p] b)) ∈ Rg.integers := by
    intro b
    let g : Γ(X p (ΓM M H) hj, ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) := ((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b)

    have hread : γ ((1 : ↥A) ⊗ₜ[R p] b) =
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom g)) := by
      apply Subtype.ext
      rw [hγ, OneMemClass.coe_one, one_smul]
      exact (𝔛.Meta_pin b).symm

    have hW := ModularCurve.XHDRModelAtP.algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
      p M H hpM hj 𝔛 θ hwgen ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) hU hwU g
    rw [hread, hW, hgauss]

    obtain ⟨-, xs, ys, hys, hgen, -, -⟩ :=
      ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
        p M hpM hpM2 H hHp A hA hj 𝔛 (algebraMap (R p) ↥A) hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ ⟨_, h₁mem⟩
        ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) hzU hneU
        (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom ((𝔛.w.hom.app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom g))
    refine ⟨xs, ys, hys, ?_⟩
    rw [← hgen]
    congr 3
    exact (GaussStalkLift.germToFunctionField_app_app_of_comp_eq gA (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) hgA₁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) _).symm

  have ha : ∀ a : ↥A, θ (γ (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj)))) ∈ Rg.integers := by
    intro a
    have : γ (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by
      apply Subtype.ext
      rw [hγ, OneMemClass.coe_one, OneMemClass.coe_one, map_one, ← HahnSeries.C_mul_eq_smul, mul_one,
        show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) from rfl,
        ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    rw [this, AlgEquiv.commutes]
    exact (Rg.algebraMap_mem_iff _).mpr a.2
  intro t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul a b =>
      have : a ⊗ₜ[R p] b = (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) * ((1 : ↥A) ⊗ₜ[R p] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, map_mul]
      exact mul_mem (ha a) (hb b)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

end S4

section S5

set_option maxHeartbeats 6400000 in
theorem coe_residue_gamma_eq_mfib_reading
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A)))),
      ((Rg.residue ⟨γ t, hγG t⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm
            ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A))
              (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc).app (XFinA p M H hj A)).hom ((thetaA p M H hj A).inv t))) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)) := by
  classical
  obtain ⟨-, ⟨h₀mem, h₀pl⟩⟩ := 𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n
  obtain ⟨tκ, ht₁, -, ht₃⟩ := ht
  have hxfin : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) := by
    rw [← ht₃]
    show (tκ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    rw [ht₁, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩

  have hP₀ : (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n)) =
      (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n := by
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [base_inv_base_apply]
  have hzU : bc.base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) ∈
      XFinA p M H hj A := by
    rw [hP₀]
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).base (bc.base _) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    have hb := congrArg (fun φ => φ.base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)) hbc₁
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hb ⊢
    rw [hb]
    exact hxfin
  haveI hneU := nonempty_gA_preimage_XFinA p M H hpM hj 𝔛 A gA hgA₁
  obtain ⟨hne, xs, ys, hys, hgen, hred, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
      p M hpM hpM2 H hHp A hA hj 𝔛 (algebraMap (R p) ↥A) hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ ⟨_, h₀mem⟩
      (XFinA p M H hj A) hzU hneU ((thetaA p M H hj A).inv t)
  refine ⟨hne, ?_⟩

  have hread := read_thetaA_inv_eq p M H hpM hj 𝔛 A hA hρ gA hgA₁ hgA₂ γ hγ t
  rw [GaussStalkLift.reader_apply] at hread
  have hgen' : ((γ t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype ys = coeffMap A.subtype xs := by
    rw [← hread]; exact hgen

  obtain ⟨x', y', hx', hy', hy'0, hfxy'⟩ :=
    ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (γ t) xs ys hys hgen'
  obtain ⟨hyO, hyres⟩ := hres y' hy'
  obtain ⟨hxO, hxres⟩ := hres x' hx'
  have hmul : (⟨γ t, hγG t⟩ : ↥Rg.integers) * ⟨⟨coeffMap A.subtype y', hy'⟩, hyO⟩ = ⟨⟨coeffMap A.subtype x', hx'⟩, hxO⟩ := by
    apply Subtype.ext; apply Subtype.ext; simpa using hfxy'
  have hres' : ((Rg.residue ⟨γ t, hγG t⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' =
      coeffMap (IsLocalRing.residue ↥A) x' := by
    have h := congrArg (fun z => ((Rg.residue z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A))) hmul
    simp only [map_mul] at h
    rw [← hyres, ← hxres]
    simpa using h

  have hcross : coeffMap (IsLocalRing.residue ↥A) xs * coeffMap (IsLocalRing.residue ↥A) y' =
      coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) ys := by
    have hA' : coeffMap A.subtype (xs * y') = coeffMap A.subtype (x' * ys) := by
      rw [map_mul, map_mul, ← hgen', ← hfxy']; ring
    have hinj : Function.Injective (coeffMap A.subtype) := by
      intro u v huv
      ext k
      have hk := congrArg (fun z => HahnSeries.coeff z k) huv
      simp only [coeffMap_coeff] at hk
      exact hk
    have := congrArg (coeffMap (IsLocalRing.residue ↥A)) (hinj hA')
    simpa [map_mul] using this

  have hne0 : coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 := hy'0
  apply mul_right_cancel₀ hne0
  apply mul_right_cancel₀ hys
  calc ((Rg.residue ⟨γ t, hγG t⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' * coeffMap (IsLocalRing.residue ↥A) ys
      = coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) ys := by rw [hres']
    _ = coeffMap (IsLocalRing.residue ↥A) xs * coeffMap (IsLocalRing.residue ↥A) y' := hcross.symm
    _ = _ := by rw [← hred]; ring

def toSubringHom' {T F : Type*} [CommRing T] [Field F] (γ : T →+* F) (V : ValuationSubring F) (h : ∀ t, γ t ∈ V) : T →+* ↥V where
  toFun t := ⟨γ t, h t⟩
  map_one' := Subtype.ext (map_one γ)
  map_mul' a b := Subtype.ext (map_mul γ a b)
  map_zero' := Subtype.ext (map_zero γ)
  map_add' a b := Subtype.ext (map_add γ a b)

theorem germToFunctionField_app_congr {Y X : Scheme.{0}} [IsIntegral Y] {φ ψ : Y ⟶ X} (h : φ = ψ) (O : X.Opens)
    [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ O))] [Nonempty (Scheme.Opens.toScheme (ψ ⁻¹ᵁ O))] (x : Γ(X, O)) :
    Y.germToFunctionField (φ ⁻¹ᵁ O) ((φ.app O).hom x) = Y.germToFunctionField (ψ ⁻¹ᵁ O) ((ψ.app O).hom x) := by
  subst h
  rfl

theorem efib_comp0_bc_fst_w_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    :
    ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ≫ 𝔛.w.hom = ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) := by
  have hfib : XHDRLevel.fibreMap (XHDRLevel.overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) = (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) ≫ 𝔛.w.hom :=
    pullback.lift_fst _ _ _
  simp only [Category.assoc]
  rw [reassoc_of% hbc₁, hbc₁, ← 𝔛.comp_w A hA (algebraMap (R p) ↥A) hρ, Category.assoc, hfib]

set_option maxHeartbeats 3200000 in

theorem germ_comp0_wsharp_eq_germ_comp1
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (O : (X p (ΓM M H) hj).Opens) (g : Γ(X p (ΓM M H) hj, O))
    [h0 : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ O))))]
    [h1 : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ O)))] :
    (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ O)))
        ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ O))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app (𝔛.w.hom ⁻¹ᵁ O)).hom ((𝔛.w.hom.app O).hom g))) =
      (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ O))
        ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ O)).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app O).hom g)) := by

  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C ⟶ X p (ΓM M H) hj, ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) = φ₁ := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C ⟶ X p (ΓM M H) hj, ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) = ψ := ⟨_, rfl⟩
  have hφψ : φ₁ ≫ 𝔛.w.hom = ψ := by
    rw [← hφ₁, ← hψ, Category.assoc]
    exact efib_comp0_bc_fst_w_eq p M H hpM hj 𝔛 A hA hρ bc hbc₁

  haveI hφ₁ne : Nonempty (Scheme.Opens.toScheme (φ₁ ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ O))) := by
    obtain ⟨⟨z, hz⟩⟩ := h0
    refine ⟨⟨z, ?_⟩⟩
    show φ₁.base z ∈ (𝔛.w.hom ⁻¹ᵁ O)
    rw [← hφ₁, Scheme.Hom.comp_apply]
    exact hz
  haveI hψne : Nonempty (Scheme.Opens.toScheme (ψ ⁻¹ᵁ O)) := by
    obtain ⟨⟨z, hz⟩⟩ := h1
    refine ⟨⟨z, ?_⟩⟩
    show ψ.base z ∈ O
    rw [← hψ, Scheme.Hom.comp_apply]
    exact hz
  rw [GaussStalkLift.germToFunctionField_app_app_of_comp_eq ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) φ₁ hφ₁ (𝔛.w.hom ⁻¹ᵁ O),
    GaussStalkLift.germToFunctionField_app_app_of_comp_eq φ₁ 𝔛.w.hom ψ hφψ O,
    GaussStalkLift.germToFunctionField_app_app_of_comp_eq ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ψ hψ O]

theorem coe_residue_eq_of_gauss_presentation
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rg.integers) (xs ys : LaurentSeries ↥A) (hys : coeffMap (IsLocalRing.residue ↥A) ys ≠ 0)
    (hgen : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype ys = coeffMap A.subtype xs)
    (r : LaurentSeries (ResidueField ↥A)) (hred : r * coeffMap (IsLocalRing.residue ↥A) ys = coeffMap (IsLocalRing.residue ↥A) xs) :
    ((Rg.residue ⟨f, hf⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = r := by
  obtain ⟨x', y', hx', hy', hy'0, hfxy'⟩ :=
    ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA f xs ys hys hgen
  obtain ⟨hyO, hyres⟩ := hres y' hy'
  obtain ⟨hxO, hxres⟩ := hres x' hx'
  have hmul : (⟨f, hf⟩ : ↥Rg.integers) * ⟨⟨coeffMap A.subtype y', hy'⟩, hyO⟩ = ⟨⟨coeffMap A.subtype x', hx'⟩, hxO⟩ := by
    apply Subtype.ext; apply Subtype.ext; simpa using hfxy'
  have hres' : ((Rg.residue ⟨f, hf⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' =
      coeffMap (IsLocalRing.residue ↥A) x' := by
    have h := congrArg (fun z => ((Rg.residue z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A))) hmul
    simp only [map_mul] at h
    rw [← hyres, ← hxres]
    simpa using h
  have hcross : coeffMap (IsLocalRing.residue ↥A) xs * coeffMap (IsLocalRing.residue ↥A) y' =
      coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) ys := by
    have hA' : coeffMap A.subtype (xs * y') = coeffMap A.subtype (x' * ys) := by
      rw [map_mul, map_mul, ← hgen, ← hfxy']; ring
    have hinj : Function.Injective (coeffMap A.subtype) := by
      intro u v huv
      ext k
      have hk := congrArg (fun z => HahnSeries.coeff z k) huv
      simp only [coeffMap_coeff] at hk
      exact hk
    have := congrArg (coeffMap (IsLocalRing.residue ↥A)) (hinj hA')
    simpa [map_mul] using this
  apply mul_right_cancel₀ hy'0
  apply mul_right_cancel₀ hys
  calc ((Rg.residue ⟨f, hf⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' * coeffMap (IsLocalRing.residue ↥A) ys
      = coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) ys := by rw [hres']
    _ = coeffMap (IsLocalRing.residue ↥A) xs * coeffMap (IsLocalRing.residue ↥A) y' := hcross.symm
    _ = _ := by rw [← hred]; ring

set_option maxHeartbeats 6400000 in

theorem coe_residue_theta_gamma_eq_mfib_reading_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A)))),
      ((Rg.residue ⟨θ (γ t), hθγG t⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm
            ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A))
              ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app (XFinA p M H hj A)).hom ((thetaA p M H hj A).inv t))) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)) := by
  classical
  obtain ⟨⟨h₁mem, h₁pl⟩, -⟩ := 𝔛.node_pin A hA (algebraMap (R p) ↥A) hρ n
  obtain ⟨tκ, ht₁, -, ht₃⟩ := ht
  have hxfin : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) := by
    rw [← ht₃]
    show (tκ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    rw [ht₁, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  have hψ := efib_comp0_bc_fst_w_eq p M H hpM hj 𝔛 A hA hρ bc hbc₁
  have hw : 𝔛.w.hom.base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) =
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n) := by
    have hfib : XHDRLevel.fibreMap (XHDRLevel.overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) = (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) ≫ 𝔛.w.hom :=
      pullback.lift_fst _ _ _
    have h1 := congrArg (fun φ => (φ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))
      (𝔛.comp_w A hA (algebraMap (R p) ↥A) hρ)
    have h3 := congrArg (fun φ => (φ ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))).base n) (pullback.condition (f := (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)) (g := (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    simp only [Category.assoc] at h1
    rw [hfib] at h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1 h3 ⊢
    rw [h1, ← h3]
  have hP₁ : ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n)) =
      (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n) := by
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [base_inv_base_apply]
  have hzUw : bc.base (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) ∈
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) := by
    rw [hP₁]
    show 𝔛.w.hom.base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).base (bc.base _)) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    have hb := congrArg (fun φ => φ.base ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) hbc₁
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hb
    rw [hb, hw]
    exact hxfin
  have hne1 : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A))) := by
    refine ⟨⟨(inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n), ?_⟩⟩
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).base (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) ∈ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      base_inv_base_apply]
    have hb := congrArg (fun φ => φ.base ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((pullback.snd (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base n))) hbc₁
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hb
    rw [hb, hw]
    exact hxfin
  refine ⟨hne1, ?_⟩
  haveI := hne1
  haveI hU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := 𝔛.Meta_chart_nonempty
  have hneU : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))))) :=
    (ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 (algebraMap (R p) ↥A) hρ gA hgA₁ hgA₂).2.1 _ ⟨⟨_, hzUw⟩⟩
  have hwU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))) := by
    rw [← hgA₁]; exact hneU
  haveI hne_top1 : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (⊤ : (XA p M H hj A).Opens))) := ⟨⟨genericPoint _, trivial⟩⟩

  let Rr : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* LaurentSeries (ResidueField ↥A) :=
    ((qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)).toSubalgebra.toSubring.subtype.comp
      ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm.toRingHom.comp
        (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A))).hom.comp
          ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app (XFinA p M H hj A)).hom)))).comp (thetaA p M H hj A).inv.hom
  have hRr : ∀ x, Rr x = (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm
            ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A))
              ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app (XFinA p M H hj A)).hom ((thetaA p M H hj A).inv x))) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)) := fun x => rfl
  let ψG : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥Rg.integers := toSubringHom' (θ.toAlgHom.toRingHom.comp γ) Rg.integers (fun x => hθγG x)
  let Ll : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* LaurentSeries (ResidueField ↥A) :=
    (qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)).toSubalgebra.toSubring.subtype.comp ((Rg.residue).comp ψG)
  have hLl : ∀ x, Ll x = ((Rg.residue ⟨θ (γ x), hθγG x⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) := fun x => rfl
  suffices hLR : Ll = Rr by rw [← hLl, ← hRr, hLR]

  have hone : ∀ b : ↥(chartAlgFin p (ΓM M H) hj), Ll ((1 : ↥A) ⊗ₜ[R p] b) = Rr ((1 : ↥A) ⊗ₜ b) := by
    intro b
    let g : Γ(X p (ΓM M H) hj, ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) := ((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b)
    have hread : γ ((1 : ↥A) ⊗ₜ[R p] b) =
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom g)) := by
      apply Subtype.ext
      rw [hγ, OneMemClass.coe_one, one_smul]
      exact (𝔛.Meta_pin b).symm
    have hW := ModularCurve.XHDRModelAtP.algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
      p M H hpM hj 𝔛 θ hwgen ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) hU hwU g
    obtain ⟨hne0, xs, ys, hys, hgen, hred, -⟩ :=
      ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
        p M hpM hpM2 H hHp A hA hj 𝔛 (algebraMap (R p) ↥A) hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ ⟨_, h₁mem⟩
        ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) hzUw hneU
        (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom ((𝔛.w.hom.app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom g))
    haveI := hne0
    have hF : θ (γ ((1 : ↥A) ⊗ₜ[R p] b)) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom ((𝔛.w.hom.app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom g)))) := by
      rw [hread, hW]
      congr 1
      exact (GaussStalkLift.germToFunctionField_app_app_of_comp_eq gA (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) hgA₁ (𝔛.w.hom ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) _).symm
    have hgen' : ((θ (γ ((1 : ↥A) ⊗ₜ[R p] b)) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype ys = coeffMap A.subtype xs := by
      rw [hF]; exact hgen
    have hL := coe_residue_eq_of_gauss_presentation p M H hpM hpM2 A hA Rg hres (θ (γ ((1 : ↥A) ⊗ₜ[R p] b))) (hθγG _) xs ys hys hgen' _ hred
    have hsame := germ_comp0_wsharp_eq_germ_comp1 p M H hpM hj 𝔛 A hA hρ bc hbc₁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) g (h0 := hne0) (h1 := hne1)
    have hsec : (thetaA p M H hj A).inv ((1 : ↥A) ⊗ₜ[R p] b) = ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom g := by
      rw [← thetaA_section p M H hj A b, Iso.hom_inv_id_apply]
    rw [hLl, hRr, hsec, ← hsame]
    exact hL

  have hconst : ∀ a : ↥A, Ll (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) = Rr (a ⊗ₜ 1) := by
    intro a
    have hγa : γ (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by
      apply Subtype.ext
      rw [hγ, OneMemClass.coe_one, OneMemClass.coe_one, map_one, ← HahnSeries.C_mul_eq_smul, mul_one,
        show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) from rfl,
        ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    have hL : Ll (a ⊗ₜ[R p] 1) = coeffMap (IsLocalRing.residue ↥A) (HahnSeries.C a) := by
      rw [hLl]
      have : (⟨θ (γ (a ⊗ₜ[R p] 1)), hθγG _⟩ : ↥Rg.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr a.2⟩ := by
        apply Subtype.ext
        show θ (γ (a ⊗ₜ[R p] 1)) = _
        rw [hγa, AlgEquiv.commutes]
      rw [this, Rg.residue_algebraMap, HahnSeries.C_apply, coeffMap_single,
        show ((algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a) : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (IsLocalRing.residue ↥A a) from rfl,
        ModularCurve.algebraMap_laurentSeries_eq_single]
    have hsec : (thetaA p M H hj A).inv (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) =
        ((XA p M H hj A).presheaf.map (homOfLE le_top).op).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) := by
      rw [← thetaA_const p M H hj A a, Iso.hom_inv_id_apply]
    have hR : Rr (a ⊗ₜ[R p] 1) = coeffMap (IsLocalRing.residue ↥A) (HahnSeries.C a) := by
      rw [hRr, hsec]
      have hres1 := GaussStalkLift.reader_res ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm.toRingHom ⊤ (XFinA p M H hj A) le_top
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))
      simp only [GaussStalkLift.reader_apply] at hres1
      have hres1' := congrArg (fun z : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) => (z : LaurentSeries (ResidueField ↥A))) hres1
      refine hres1'.trans ?_
      have hcomp : ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ≫ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) = (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
        rw [Category.assoc, Category.assoc, hbc₂, ← Category.assoc (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1), 𝔛.comp_over A hA (algebraMap (R p) ↥A) hρ 1,
          ← Category.assoc, 𝔛.hefib A hA (algebraMap (R p) ↥A) hρ]
      have h1 := GaussStalkLift.ScalarReadAux.germToFunctionField_app_appTop_eq_of_comp_eq ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))) _ hcomp
        ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)
      have h2 : ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.presheaf.germ ⊤ (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) trivial).hom
          (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) =
          AlgebraicCurve.baseToFunctionField (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase (IsLocalRing.residue ↥A a) := by
        rw [GaussStalkLift.ScalarReadAux.appTop_comp_apply, GaussStalkLift.ScalarReadAux.appTop_specMap_ΓSpecIso_inv (IsLocalRing.residue ↥A) a]
        rfl
      have h3 : (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ ⊤)
          ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) =
          algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (IsLocalRing.residue ↥A a) :=
        (congrArg ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm) (h1.trans h2)).trans ((RingEquiv.symm_apply_eq _).mpr ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv_algebraMap _).symm)
      show (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm.toRingHom ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ ⊤)
          ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) = _
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h3, HahnSeries.C_apply, coeffMap_single,
        show ((algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (IsLocalRing.residue ↥A a) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (IsLocalRing.residue ↥A a) from rfl,
        ModularCurve.algebraMap_laurentSeries_eq_single]
    rw [hL, hR]
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
      have : a ⊗ₜ[R p] b = (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) * ((1 : ↥A) ⊗ₜ[R p] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, map_mul, hconst, hone]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end S5

end BranchReadSkel
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

namespace BranchReadF

open ModularCurve AlgebraicCurve BranchReadSkel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1600000 in

theorem isRadical_map_maximalIdeal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers) :
    ((IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))).IsRadical := by

  haveI hfib : IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) := 𝔛.fibre_reduced A hA (algebraMap (R p) ↥A) hρ

  have θκ := BranchReadSkel.θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
    (𝟙 (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))) (K := ResidueField ↥A)
  haveI hκB : IsReduced (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
    isReduced_of_injective θκ.commRingCatIsoToRingEquiv.symm θκ.commRingCatIsoToRingEquiv.symm.injective

  have hsurj : Function.Surjective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) :=
    Algebra.TensorProduct.map_surjective (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj)) IsLocalRing.residue_surjective Function.surjective_id
  have hker : RingHom.ker (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) =
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) := by

    apply le_antisymm
    · rw [Algebra.TensorProduct.rTensor_ker (R := R p) (C := ↥(chartAlgFin p (ΓM M H) hj)) (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) IsLocalRing.residue_surjective]
      refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      have ha' : a ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [RingHom.mem_ker] at ha
        exact (IsLocalRing.residue_eq_zero_iff a).mp ha
      exact Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ ha')
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul,
        map_one]
      have : (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
      rw [this, TensorProduct.zero_tmul]

  rw [← hker]
  exact (RingHom.ker_isRadical_iff_reduced_of_surjective hsurj).mpr hκB

end BranchReadF
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

namespace BranchReadE2

theorem inf_le_of_forall_prime_le {R : Type*} [CommRing R] (I J N : Ideal R) (hN : N.IsRadical)
    (hcover : ∀ P : Ideal R, P.IsPrime → N ≤ P → I ≤ P ∨ J ≤ P) (hI : N ≤ I) (hJ : N ≤ J) : I ⊓ J = N := by
  apply le_antisymm
  · intro x hx
    apply hN
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hNP, hP⟩
    rcases hcover P hP hNP with h | h
    · exact h hx.1
    · exact h hx.2
  · exact le_inf hI hJ

theorem map_maximalIdeal_localization_eq {T : Type*} [CommRing T] (𝔯₀ 𝔯₁ : Ideal T) [𝔯₀.IsPrime] [𝔯₁.IsPrime]
    (N : Ideal T) (hb : N = 𝔯₀ ⊓ 𝔯₁) (hnc : ¬ 𝔯₁ ≤ 𝔯₀) :
    N.map (algebraMap T (Localization.AtPrime 𝔯₀)) = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) := by
  subst hb
  apply le_antisymm
  · calc (𝔯₀ ⊓ 𝔯₁).map (algebraMap T (Localization.AtPrime 𝔯₀)) ≤ 𝔯₀.map (algebraMap T (Localization.AtPrime 𝔯₀)) :=
          Ideal.map_mono inf_le_left
      _ = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) := Localization.AtPrime.map_eq_maximalIdeal
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hs1, hs0⟩ := SetLike.not_le_iff_exists.mp hnc
    have hu : IsUnit (algebraMap T (Localization.AtPrime 𝔯₀) s) :=
      IsLocalization.map_units (Localization.AtPrime 𝔯₀) (⟨s, hs0⟩ : 𝔯₀.primeCompl)
    rw [Ideal.mem_comap]
    have hxs : algebraMap T (Localization.AtPrime 𝔯₀) (x * s) ∈ (𝔯₀ ⊓ 𝔯₁).map (algebraMap T (Localization.AtPrime 𝔯₀)) :=
      Ideal.mem_map_of_mem _ ⟨𝔯₀.mul_mem_right s hx, 𝔯₁.mul_mem_left x hs1⟩
    rw [map_mul] at hxs
    have := Ideal.mul_mem_right ((hu.unit⁻¹ : (Localization.AtPrime 𝔯₀)ˣ) : Localization.AtPrime 𝔯₀) _ hxs
    rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this

end BranchReadE2
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

namespace BranchReadE3

open ModularCurve AlgebraicCurve BranchReadSkel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem closure_singleton_genericPoint_eq_range {C Y : Scheme.{0}} [IsIntegral C] (φ : C ⟶ Y) [IsClosedImmersion φ] :
    closure ({φ.base (genericPoint C)} : Set Y) = Set.range φ.base := by
  apply le_antisymm
  · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) φ.isClosedEmbedding.isClosed_range
  · rintro _ ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map φ.continuous).mem_closure

theorem not_specializes_of_isClosedImmersion {C Y : Scheme.{0}} [IsIntegral C]
    (hC : ∀ y : C, y ≠ genericPoint C → IsClosed ({y} : Set C))
    (φ ψ : C ⟶ Y) [IsClosedImmersion φ] [IsClosedImmersion ψ]
    (hne : Set.range φ.base ≠ Set.range ψ.base) : ¬ (φ.base (genericPoint C) ⤳ ψ.base (genericPoint C)) := by
  intro hsp
  have hclφ := closure_singleton_genericPoint_eq_range φ
  have hclψ := closure_singleton_genericPoint_eq_range ψ
  have hmem : ψ.base (genericPoint C) ∈ Set.range φ.base := by
    rw [← hclφ]; exact hsp.mem_closure
  obtain ⟨y, hy⟩ := hmem
  by_cases hyη : y = genericPoint C
  · subst hyη
    apply hne
    rw [← hclφ, ← hclψ, hy]
  · have hcl : IsClosed ({ψ.base (genericPoint C)} : Set Y) := by
      rw [← hy, ← Set.image_singleton]
      exact φ.isClosedEmbedding.isClosedMap _ (hC y hyη)
    have hrange : Set.range ψ.base = {ψ.base (genericPoint C)} := by
      rw [← hclψ, hcl.closure_eq]
    have hψy : ψ.base y ∈ ({ψ.base (genericPoint C)} : Set Y) := hrange ▸ ⟨y, rfl⟩
    exact hyη (ψ.isClosedEmbedding.injective (Set.mem_singleton_iff.mp hψy))

theorem genericPoint_mem_of_nonempty {C : Scheme.{0}} [IsIntegral C] (U : C.Opens) (h : Nonempty (Scheme.Opens.toScheme U)) :
    genericPoint C ∈ U := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ x, hx⟩

theorem mem_basicOpen_genericPoint_iff {C : Scheme.{0}} [IsIntegral C] (U : C.Opens) [hU : Nonempty (Scheme.Opens.toScheme U)] (s : Γ(C, U)) :
    genericPoint C ∈ C.basicOpen s ↔ C.germToFunctionField U s ≠ 0 := by
  rw [Scheme.mem_basicOpen _ s _ (genericPoint_mem_of_nonempty U hU), isUnit_iff_ne_zero]

section BC

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]
  (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
  (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
  (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

include hbc₁ hbc₂ in
omit [Fact p.Prime] [NeZero M] in
theorem isPullback_bc : IsPullback bc (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) := by
  have hig : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have s : IsPullback (bc ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))))
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))
      (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))) := by
    rw [hbc₁, hig]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right s hbc₂ (IsPullback.of_hasPullback _ _)

include hbc₁ hbc₂ in
omit [Fact p.Prime] [NeZero M] in
theorem isClosedImmersion_bc : IsClosedImmersion bc := by
  have hi : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) (isPullback_bc p M H hj A bc hbc₁ hbc₂).flip hi

end BC
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section ChartPt

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

abbrev gChartA : Spec (CommRingCat.of (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ XA p M H hj A :=
  gChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A))

omit [Fact p.Prime] [NeZero M] in
theorem exists_gChartA_eq (ξ : ↥(XA p M H hj A)) (hξ : ξ ∈ XFinA p M H hj A) : ∃ 𝔮, (gChartA p M H hj A).base 𝔮 = ξ := by
  have h : ξ ∈ (gChartA p M H hj A).opensRange := by
    rw [opensRange_gChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A))]
    exact hξ
  exact h

theorem gChartA_mem_basicOpen_iff (c : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (𝔮 : ↥(Spec (CommRingCat.of (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))))) :
    (gChartA p M H hj A).base 𝔮 ∈ (XA p M H hj A).basicOpen ((thetaA p M H hj A).inv c) ↔ c ∉ 𝔮.asIdeal := by
  have h1 : (gChartA p M H hj A).base 𝔮 =
      (isAffineOpen_XFinA p M H hj A).fromSpec.base ((Spec.map (thetaA p M H hj A).hom).base 𝔮) :=
    (fromSpec_specθ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (𝟙 (XA p M H hj A)) 𝔮).symm
  have h2 : (isAffineOpen_XFinA p M H hj A).fromSpec.base ((Spec.map (thetaA p M H hj A).hom).base 𝔮) ∈ (XA p M H hj A).basicOpen ((thetaA p M H hj A).inv c) ↔
      (Spec.map (thetaA p M H hj A).hom).base 𝔮 ∈ (isAffineOpen_XFinA p M H hj A).fromSpec ⁻¹ᵁ (XA p M H hj A).basicOpen ((thetaA p M H hj A).inv c) := Iff.rfl
  rw [h1, h2, IsAffineOpen.fromSpec_preimage_basicOpen]
  show (thetaA p M H hj A).inv c ∉ Ideal.comap (thetaA p M H hj A).hom.hom 𝔮.asIdeal ↔ _
  rw [Ideal.mem_comap]
  show ¬ ((thetaA p M H hj A).inv ≫ (thetaA p M H hj A).hom).hom c ∈ 𝔮.asIdeal ↔ _
  rw [Iso.inv_hom_id]
  rfl

end ChartPt
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

set_option maxHeartbeats 6400000 in
theorem not_le_branch_primes
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers) :
    ¬ 𝔯₀ ≤ 𝔯₁ ∧ ¬ 𝔯₁ ≤ 𝔯₀ := by
  classical

  have h0 : ∀ t, t ∈ 𝔯₀ ↔ (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) ∉
      (XA p M H hj A).basicOpen ((thetaA p M H hj A).inv t) := by
    intro t
    obtain ⟨hne, hread⟩ := coe_residue_gamma_eq_mfib_reading p M H hpM hpM2 hHp hj 𝔛 A hA hρ γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ t
    haveI := hne
    rw [h𝔯₀def, ← Rg.ker_residue, RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero, hread, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm.injective,
      ← not_iff_not, not_not, ← ne_eq, ← mem_basicOpen_genericPoint_iff, ← Scheme.preimage_basicOpen]
    rfl
  have h1 : ∀ t, t ∈ 𝔯₁ ↔ (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1 ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) ∉
      (XA p M H hj A).basicOpen ((thetaA p M H hj A).inv t) := by
    intro t
    obtain ⟨hne, hread⟩ := coe_residue_theta_gamma_eq_mfib_reading_one p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ hθγG t
    haveI := hne
    rw [h𝔯₁def, ← Rg.ker_residue, RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero, hread, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm.injective,
      ← not_iff_not, not_not, ← ne_eq, ← mem_basicOpen_genericPoint_iff, ← Scheme.preimage_basicOpen]
    rfl

  have hξ0 : (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) ∈ XFinA p M H hj A := by
    obtain ⟨hne, -⟩ := coe_residue_gamma_eq_mfib_reading p M H hpM hpM2 hHp hj 𝔛 A hA hρ γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ 0
    exact genericPoint_mem_of_nonempty _ hne
  have hξ1 : (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1 ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) ∈ XFinA p M H hj A := by
    obtain ⟨hne, -⟩ := coe_residue_theta_gamma_eq_mfib_reading_one p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ hθγG 0
    exact genericPoint_mem_of_nonempty _ hne
  obtain ⟨𝔮₀, hq0⟩ := exists_gChartA_eq p M H hj A _ hξ0
  obtain ⟨𝔮₁, hq1⟩ := exists_gChartA_eq p M H hj A _ hξ1
  have hr0 : ∀ t, t ∈ 𝔯₀ ↔ t ∈ 𝔮₀.asIdeal := fun t => by
    rw [h0, ← hq0, gChartA_mem_basicOpen_iff, not_not]
  have hr1 : ∀ t, t ∈ 𝔯₁ ↔ t ∈ 𝔮₁.asIdeal := fun t => by
    rw [h1, ← hq1, gChartA_mem_basicOpen_iff, not_not]

  haveI := isClosedImmersion_bc p M H hj A bc hbc₁ hbc₂
  haveI := 𝔛.comp_isClosedImmersion A hA (algebraMap (R p) ↥A) hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA (algebraMap (R p) ↥A) hρ 1
  haveI i0 : IsClosedImmersion (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc) := inferInstance
  haveI i1 : IsClosedImmersion (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1 ≫ bc) := inferInstance
  have hrange : ∀ i : Fin 2, Set.range (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ i ≫ bc).base =
      bc.base '' Set.range (𝔛.comp A hA (algebraMap (R p) ↥A) hρ i).base := by
    intro i
    ext z
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.mem_range, Function.comp_apply, Set.mem_image]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      obtain ⟨y, rfl⟩ := (𝔛.efib A hA (algebraMap (R p) ↥A) hρ).surjective x
      exact ⟨y, rfl⟩
  have hne01 : Set.range (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0 ≫ bc).base ≠
      Set.range (𝔛.efib A hA (algebraMap (R p) ↥A) hρ ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1 ≫ bc).base := by
    rw [hrange 0, hrange 1]
    intro heq
    exact 𝔛.range_comp_ne A hA (algebraMap (R p) ↥A) hρ ((bc.isClosedEmbedding.injective.image_injective) heq)
  have hC : ∀ y : ↥(𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C, y ≠ genericPoint _ → IsClosed ({y} : Set _) := fun y hy =>
    AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase y hy

  refine ⟨fun hle => ?_, fun hle => ?_⟩
  · have hsp : 𝔮₀ ⤳ 𝔮₁ := (PrimeSpectrum.le_iff_specializes 𝔮₀ 𝔮₁).mp (fun t ht => (hr1 t).mp (hle ((hr0 t).mpr ht)))
    have hsp' := hsp.map (gChartA p M H hj A).continuous
    rw [hq0, hq1] at hsp'
    exact not_specializes_of_isClosedImmersion hC _ _ hne01 hsp'
  · have hsp : 𝔮₁ ⤳ 𝔮₀ := (PrimeSpectrum.le_iff_specializes 𝔮₁ 𝔮₀).mp (fun t ht => (hr0 t).mp (hle ((hr1 t).mpr ht)))
    have hsp' := hsp.map (gChartA p M H hj A).continuous
    rw [hq0, hq1] at hsp'
    exact not_specializes_of_isClosedImmersion hC _ _ hne01.symm hsp'

end BranchReadE3
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

noncomputable section
namespace BranchReadF

open ModularCurve AlgebraicCurve BranchReadSkel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section GenericId

universe u

variable {R K B : Type u} [CommRing R] [CommRing K] [CommRing B] [Algebra R K] [Algebra R B]
  {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
  (ιB : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ιB]
  (hιB : ιB ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

theorem fromSpec_specθ_id (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (isAffineOpen_U c ιB hιB (𝟙 _)).fromSpec (Spec.map (BranchReadSkel.θ c ιB hιB (𝟙 _)).hom 𝔮') = bcChart c ιB hιB (K := K) 𝔮' := by
  rw [fromSpec_specθ, gChart, IsIso.inv_id, Category.comp_id]

end GenericId
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section CoverAux

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

theorem fromSpec_spec_thetaA (𝔮 : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) :
    (isAffineOpen_XFinA p M H hj A).fromSpec (Spec.map (thetaA p M H hj A).hom 𝔮) = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)) 𝔮 := by
  have h := fromSpec_specθ_id (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) 𝔮 (K := ↥A)
  first | exact h | simpa only [Category.id_comp] using h | (simp only [Category.id_comp] at h; exact h) | (simp only [Category.id_comp]; exact h) | (simp only [Category.id_comp] at h ⊢; exact h)

theorem thetaA_hom_mem_asIdeal_of_app_eq_zero
    {G : Scheme} (g : G ⟶ XA p M H hj A) (m : G) (𝔮 : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))
    (hm : g.base m = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base 𝔮)
    (s : Γ(XA p M H hj A, (XFinA p M H hj A))) (hs : (g.app (XFinA p M H hj A)).hom s = 0) :
    (thetaA p M H hj A).hom s ∈ 𝔮.asIdeal := by

  have hnot : g.base m ∉ (XA p M H hj A).basicOpen s := by
    intro hmem
    have h' : m ∈ g ⁻¹ᵁ ((XA p M H hj A).basicOpen s) := hmem
    rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero] at h'
    exact h'
  rw [hm, ← fromSpec_spec_thetaA] at hnot
  have h2 : Spec.map (thetaA p M H hj A).hom 𝔮 ∉ (isAffineOpen_XFinA p M H hj A).fromSpec ⁻¹ᵁ ((XA p M H hj A).basicOpen s) := hnot
  rw [IsAffineOpen.fromSpec_preimage_basicOpen] at h2
  have h3 : s ∈ (Spec.map (thetaA p M H hj A).hom 𝔮).asIdeal := not_not.mp fun hns => h2 ((PrimeSpectrum.mem_basicOpen _ _).mpr hns)
  exact h3

end CoverAux
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section FibrePoint

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

set_option maxHeartbeats 3200000 in

theorem specMap_comp_bcChart_eq_bcChart_comp (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :
    Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ≫ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)) = (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) bc) := by

  have hKfst : (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj :=
    bcChart_fst (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
  have hKsnd : ∀ {Z : Scheme} (h : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Z),
      (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) ≫ h)) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) ≫ h := by
    intro Z h
    have h0 : (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) :=
      bcChart_snd (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
    rw [← Category.assoc, h0]

  have hR : (((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).comp (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom = (Algebra.TensorProduct.includeRight (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom := by
    ext b
    show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) ((1 : ↥A) ⊗ₜ[R p] b) = (1 : ResidueField ↥A) ⊗ₜ[R p] b
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hL : (((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).comp (IsLocalRing.residue ↥A) := by
    ext a
    show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) = (IsLocalRing.residue ↥A a) ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hbc₁, hKfst, bcChart_fst, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hR]
  · rw [Category.assoc, Category.assoc, hbc₂, hKsnd, bcChart_snd, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hL]

set_option maxHeartbeats 3200000 in

theorem exists_fibre_point_bc_eq_bcChart (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) [hP : P.IsPrime]
    (hle : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ P) :
    ∃ z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))), bc.base z = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base ⟨P, hP⟩ := by
  classical

  have hsurj : Function.Surjective ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
    Algebra.TensorProduct.map_surjective (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj)) IsLocalRing.residue_surjective Function.surjective_id
  have hkerA : RingHom.ker (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) =
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) := by

    apply le_antisymm
    · rw [Algebra.TensorProduct.rTensor_ker (R := R p) (C := ↥(chartAlgFin p (ΓM M H) hj)) (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) IsLocalRing.residue_surjective]
      refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      have ha' : a ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [RingHom.mem_ker] at ha
        exact (IsLocalRing.residue_eq_zero_iff a).mp ha
      exact Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ ha')
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul,
        map_one]
      have : (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
      rw [this, TensorProduct.zero_tmul]
  have hkerP : RingHom.ker ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ≤ P := by rw [RingHom.ker_coe_toRingHom, hkerA]; exact hle

  haveI hP' : (P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkerP
  have hcomap : (P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).comap ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj]
    exact sup_eq_left.mpr hkerP
  have h𝔮 : (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))).base (⟨P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), hP'⟩ : PrimeSpectrum (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) =
      (⟨P, hP⟩ : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) :=
    PrimeSpectrum.ext hcomap

  refine ⟨(bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)).base ⟨P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), hP'⟩, ?_⟩
  have h := congrArg (fun φ => φ.base (⟨P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), hP'⟩ : PrimeSpectrum (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))))
    (specMap_comp_bcChart_eq_bcChart_comp p M H hj A bc hbc₁ hbc₂)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [h𝔮] at h
  exact h.symm

end FibrePoint
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section Vanishing

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

theorem section_eq_zero_of_coe_reading_eq_zero (U : (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
    (x : Γ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C, U))
    (h0 : (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField U x) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
      LaurentSeries (ResidueField ↥A)) = 0) :
    x = 0 := by
  have h1 := (ZeroMemClass.coe_eq_zero).mp h0
  have h2 := (map_eq_zero_iff _ (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm.injective).mp h1
  exact Scheme.germToFunctionField_injective _ _ (h2.trans (map_zero _).symm)

end Vanishing
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section Key

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

set_option maxHeartbeats 1600000 in

theorem le_of_forall_app_thetaA_inv_eq_zero
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) [hP : P.IsPrime]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))) (hzx : bc.base z = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base ⟨P, hP⟩)
    (i : Fin 2) (y₀ : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))) (hy₀ : (𝔛.comp A hA (algebraMap (R p) ↥A) hρ i).base y₀ = z)
    (𝔯 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (happ : ∀ t ∈ 𝔯, ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ i) ≫ bc)).app (XFinA p M H hj A)).hom ((thetaA p M H hj A).inv t) = 0) : 𝔯 ≤ P := by
  intro t htr
  have hm : ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ i) ≫ bc).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base y₀) = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base ⟨P, hP⟩ := by
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [BranchReadSkel.base_inv_base_apply, hy₀, hzx]
  have h := thetaA_hom_mem_asIdeal_of_app_eq_zero p M H hj A ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ i) ≫ bc) ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base y₀) ⟨P, hP⟩ hm ((thetaA p M H hj A).inv t) (happ t htr)
  rw [Iso.inv_hom_id_apply] at h
  exact h

end Key
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

set_option maxHeartbeats 3200000 in

theorem cover_of_prime_over_of_R1
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (hR1 : ∀ t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), ∃ (_ : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A)))),
      ((Rg.residue ⟨θ (γ t), hθγG t⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        (((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).ffEquiv.symm
            ((𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C.germToFunctionField (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc) ⁻¹ᵁ (XFinA p M H hj A))
              ((((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ bc).app (XFinA p M H hj A)).hom ((thetaA p M H hj A).inv t))) : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A))) :
    ∀ P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), P.IsPrime →
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ P →
      𝔯₀ ≤ P ∨ 𝔯₁ ≤ P := by
  classical
  intro P hP hle

  obtain ⟨z, hzx⟩ := exists_fibre_point_bc_eq_bcChart p M H hj A bc hbc₁ hbc₂ P hle

  rcases 𝔛.comp_jointly_surjective A hA (algebraMap (R p) ↥A) hρ z with ⟨y₀, hy₀⟩ | ⟨y₀, hy₀⟩
  · left
    refine le_of_forall_app_thetaA_inv_eq_zero p M H hpM hj 𝔛 A hA hρ bc P z hzx 0 y₀ hy₀ 𝔯₀ fun t htr => ?_
    obtain ⟨hne, hR0⟩ := BranchReadSkel.coe_residue_gamma_eq_mfib_reading p M H hpM hpM2 hHp hj 𝔛 A hA hρ γ hγ n χκ ht Rg hgauss hres hγG
      gA hgA₁ hgA₂ bc hbc₁ hbc₂ t
    have hres0 : Rg.residue ⟨γ t, hγG t⟩ = 0 := by
      have h := (h𝔯₀def t).mp htr
      rw [← Rg.ker_residue] at h
      exact RingHom.mem_ker.mp h
    rw [hres0, ZeroMemClass.coe_zero] at hR0
    exact section_eq_zero_of_coe_reading_eq_zero p M H hpM hj 𝔛 A hA hρ _ _ hR0.symm
  · right
    refine le_of_forall_app_thetaA_inv_eq_zero p M H hpM hj 𝔛 A hA hρ bc P z hzx 1 y₀ hy₀ 𝔯₁ fun t htr => ?_
    obtain ⟨hne, hR1t⟩ := hR1 t
    have hres0 : Rg.residue ⟨θ (γ t), hθγG t⟩ = 0 := by
      have h := (h𝔯₁def t).mp htr
      rw [← Rg.ker_residue] at h
      exact RingHom.mem_ker.mp h
    rw [hres0, ZeroMemClass.coe_zero] at hR1t
    exact section_eq_zero_of_coe_reading_eq_zero p M H hpM hj 𝔛 A hA hρ _ _ hR1t.symm

set_option maxHeartbeats 1600000 in

theorem cover_of_prime_over
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers) :
    ∀ P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), P.IsPrime →
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ P →
      𝔯₀ ≤ P ∨ 𝔯₁ ≤ P := by
  exact cover_of_prime_over_of_R1 p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂
    hθγG 𝔯₀ h𝔯₀def 𝔯₁ h𝔯₁def
    (fun t => BranchReadSkel.coe_residue_theta_gamma_eq_mfib_reading_one p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht
      Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ hθγG t)

end BranchReadF
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"
end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

namespace BranchReadSkel

open ModularCurve AlgebraicCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section S6pending

set_option maxHeartbeats 3200000 in
private theorem _root_.BranchReadSkel.cover_of_prime_over
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers) :
    ∀ P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), P.IsPrime →
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ P →
      𝔯₀ ≤ P ∨ 𝔯₁ ≤ P :=
  BranchReadF.cover_of_prime_over p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ hθγG 𝔯₀ h𝔯₀def 𝔯₁ h𝔯₁def

p2m_export "BranchReadSkel" "cover_of_prime_over"
set_option maxHeartbeats 3200000 in
private theorem _root_.BranchReadSkel.not_le_branch_primes
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
    (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (n : ↥(pullback (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)))
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t, γ t ∈ Rg.integers)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (hθγG : ∀ t, θ (γ t) ∈ Rg.integers)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    (𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers) :
    ¬ 𝔯₀ ≤ 𝔯₁ ∧ ¬ 𝔯₁ ≤ 𝔯₀ :=
  BranchReadE3.not_le_branch_primes p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG gA hgA₁ hgA₂ bc hbc₁ hbc₂ hθγG 𝔯₀ h𝔯₀def 𝔯₁ h𝔯₁def

p2m_export "BranchReadSkel" "not_le_branch_primes"
end S6pending
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section Bridge

variable {F : Type*} [Field F]

theorem valuationSubring_isUnit_iff (W : ValuationSubring F) (x : F) (hx : x ∈ W) :
    IsUnit (⟨x, hx⟩ : ↥W) ↔ x ≠ 0 ∧ x⁻¹ ∈ W := by
  constructor
  · intro hu
    have hx0 : x ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
    refine ⟨hx0, ?_⟩
    have hinv : ((hu.unit⁻¹ : (↥W)ˣ) : ↥W).1 = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      have hu' := congrArg Subtype.val hu.unit.mul_inv
      rw [IsUnit.unit_spec] at hu'
      exact hu'
    rw [← hinv]; exact ((hu.unit⁻¹ : (↥W)ˣ) : ↥W).2
  · rintro ⟨hx0, hinv⟩
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem mem_maximalIdeal_comap_iff (W : ValuationSubring F) (θ : F ≃+* F) (x : F) (hx : x ∈ W.comap θ.toRingHom) :
    (⟨x, hx⟩ : ↥(W.comap θ.toRingHom)) ∈ IsLocalRing.maximalIdeal ↥(W.comap θ.toRingHom) ↔
      (⟨θ x, hx⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not,
    valuationSubring_isUnit_iff, valuationSubring_isUnit_iff]
  show x ≠ 0 ∧ θ.toRingHom x⁻¹ ∈ W ↔ θ x ≠ 0 ∧ (θ x)⁻¹ ∈ W
  rw [map_inv₀, map_ne_zero_iff _ θ.injective]
  rfl

theorem mem_nonunits_comap_iff (W : ValuationSubring F) (θ : F ≃+* F) (x : F) :
    x ∈ (W.comap θ.toRingHom).nonunits ↔ θ x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨h, hm⟩; exact ⟨h, (mem_maximalIdeal_comap_iff W θ x h).mp hm⟩
  · rintro ⟨h, hm⟩; exact ⟨h, (mem_maximalIdeal_comap_iff W θ x h).mpr hm⟩

end Bridge
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

section S3
variable {F T : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {A : ValuationSubring (AlgebraicClosure ℚ)} [CommRing T]

theorem comap_branch_eq_maximalIdeal (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (ι : ↥A →+* T) (hγA : ∀ a : ↥A, γ (ι a) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W) :
    𝔯.comap ι = IsLocalRing.maximalIdeal ↥A := by
  ext a
  rw [Ideal.mem_comap, h𝔯def, ← hW𝔪 a]
  have hmem : (⟨γ (ι a), hγW (ι a)⟩ : ↥W) = ⟨algebraMap (AlgebraicClosure ℚ) F a, hWA a⟩ := Subtype.ext (hγA a)
  rw [hmem]

theorem map_maximalIdeal_le_branch (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (ι : ↥A →+* T) (hγA : ∀ a : ↥A, γ (ι a) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W) :
    (IsLocalRing.maximalIdeal ↥A).map ι ≤ 𝔯 := by
  rw [Ideal.map_le_iff_le_comap, comap_branch_eq_maximalIdeal W γ hγW ι hγA hWA hW𝔪 𝔯 h𝔯def]

theorem mem_of_fraction (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    (h : F) (a c : T) (hc : c ∉ 𝔯) (hfac : h * γ c = γ a) : h ∈ W := by
  rw [h𝔯def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
  have hc0 : γ c ≠ 0 := by
    intro h0
    apply hc.ne_zero
    exact Subtype.ext h0
  have hh : h = γ a * (γ c)⁻¹ := by rw [← hfac, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  have hinv : ((hc.unit⁻¹ : (↥W)ˣ) : ↥W).1 = (γ c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have hu := congrArg Subtype.val hc.unit.mul_inv
    rw [IsUnit.unit_spec] at hu
    exact hu
  rw [hh, ← hinv]
  exact mul_mem (hγW a) ((hc.unit⁻¹ : (↥W)ˣ) : ↥W).2

theorem regularProlongation_maximalIdeal_iff {Fb : Type*} [Field Fb] [Algebra (ResidueField ↥A) Fb]
    (Rg : RegularProlongation A F Fb) (a : ↥A) :
    (⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff a).mpr a.2⟩ : ↥Rg.integers) ∈
        IsLocalRing.maximalIdeal ↥Rg.integers ↔ a ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [← Rg.ker_residue, RingHom.mem_ker, Rg.residue_algebraMap, map_eq_zero_iff _ (algebraMap (ResidueField ↥A) Fb).injective,
    IsLocalRing.residue_eq_zero_iff]

end S3
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

theorem natCast_mem_nonunits_integers
    (p : ℕ) [Fact p.Prime] {F Fb : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] [Field Fb]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (ResidueField ↥A) Fb] [CharP (ResidueField ↥A) p]
    (Rg : RegularProlongation A F Fb) :
    (algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ)) ∈ Rg.integers.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨(Rg.algebraMap_mem_iff _).mpr (natCast_mem A p), ?_⟩
  rw [← Rg.ker_residue, RingHom.mem_ker]
  have : (⟨algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr (natCast_mem A p)⟩ : ↥Rg.integers) =
      ⟨algebraMap (AlgebraicClosure ℚ) F (((p : ℕ) : ↥A) : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr ((p : ℕ) : ↥A).2⟩ :=
    Subtype.ext (by simp)
  rw [this, Rg.residue_algebraMap, map_natCast, CharP.cast_eq_zero (ResidueField ↥A) p, map_zero]

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
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

theorem finiteType_chartAlgFin (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj) :=
  haveI : (ΓM M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H)
    (ModularCurve.translation_mem_GammaH M H) (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1

section H3

theorem eq_zero_of_hasValue_zero {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (c : K)
    (h : v.HasValue 0 c) : c = 0 := by
  obtain ⟨h0, hres⟩ := h
  have : (⟨(0 : L), h0⟩ : ↥v.toValuationSubring) = 0 := Subtype.ext rfl
  rw [this, map_zero] at hres
  exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres.symm

set_option maxHeartbeats 6400000 in
theorem exists_snd_branch_min
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
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

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔔 : 𝔔.IsPrime) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), γ t ∈ Rg.integers)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), s ≠ 0 ∧ e * γ s = γ a)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    [h𝔯₀p : 𝔯₀.IsPrime] :
    ∃ 𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), 𝔯₁.IsPrime ∧ 𝔯₀ ≤ 𝔔 ∧ 𝔯₁ ≤ 𝔔 ∧ ¬ 𝔯₀ ≤ 𝔯₁ ∧ ¬ 𝔯₁ ≤ 𝔯₀ ∧
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = 𝔯₀ ⊓ 𝔯₁ ∧
      (∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)) ∧
      (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯₀)).comp
          (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) =
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) := by
  classical
  subst halg

  have hgA₁ := gA_fst p M H hj 𝔛 A hρ
  have hgA₂ := gA_snd p M H hj 𝔛 A hρ
  have hbc₁ := bc_fst p M H hj A
  have hbc₂ := bc_snd p M H hj A

  have hθγG : ∀ t, θ (γ t) ∈ Rg.integers :=
    theta_gamma_mem_integers p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss
      (gA p M H hj 𝔛 A hρ) hgA₁ hgA₂ (bc p M H hj A) hbc₁ hbc₂
  let 𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := (IsLocalRing.maximalIdeal ↥Rg.integers).comap (toSubringHom' (θ.toAlgHom.toRingHom.comp γ) Rg.integers hθγG)
  have h𝔯₁def : ∀ t, t ∈ 𝔯₁ ↔ (⟨θ (γ t), hθγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers := fun t => Iff.rfl
  haveI h𝔯₁p : 𝔯₁.IsPrime := Ideal.comap_isPrime _ _

  have hγA : ∀ a : ↥A, γ (Algebra.TensorProduct.includeLeftRingHom a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by
    intro a
    apply Subtype.ext
    show ((γ (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [hγ, OneMemClass.coe_one, OneMemClass.coe_one, map_one, ← HahnSeries.C_mul_eq_smul, mul_one,
      show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) from rfl,
      ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  have hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ Rg.integers := fun a => (Rg.algebraMap_mem_iff a).mpr a.2

  have hN0 : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ 𝔯₀ :=
    map_maximalIdeal_le_branch Rg.integers γ hγG _ hγA hWA (regularProlongation_maximalIdeal_iff Rg) 𝔯₀ h𝔯₀def

  let W₁ : ValuationSubring ↥(xHFunctionFieldBar M H) := Rg.integers.comap θ.toRingEquiv.toRingHom
  have hγW : ∀ t, γ t ∈ W₁ := fun t => hθγG t
  have hWA₁ : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ W₁ := by
    intro a; show θ (algebraMap _ _ (a : AlgebraicClosure ℚ)) ∈ Rg.integers; rw [AlgEquiv.commutes]; exact hWA a
  have hW𝔪₁ : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), hWA₁ a⟩ : ↥W₁) ∈ IsLocalRing.maximalIdeal ↥W₁ ↔
      a ∈ IsLocalRing.maximalIdeal ↥A := by
    intro a
    rw [mem_maximalIdeal_comap_iff Rg.integers θ.toRingEquiv _ (hWA₁ a)]
    have : (⟨θ.toRingEquiv (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)), hWA₁ a⟩ : ↥Rg.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff a).mpr a.2⟩ :=
      Subtype.ext (AlgEquiv.commutes θ _)
    rw [this]
    exact regularProlongation_maximalIdeal_iff Rg a
  have h𝔯₁def' : ∀ t, t ∈ 𝔯₁ ↔ (⟨γ t, hγW t⟩ : ↥W₁) ∈ IsLocalRing.maximalIdeal ↥W₁ := fun t =>
    (h𝔯₁def t).trans (mem_maximalIdeal_comap_iff Rg.integers θ.toRingEquiv (γ t) (hγW t)).symm
  have hN1 : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ 𝔯₁ :=
    map_maximalIdeal_le_branch W₁ γ hγW _ hγA hWA₁ hW𝔪₁ 𝔯₁ h𝔯₁def'
  have hrad := BranchReadF.isRadical_map_maximalIdeal p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG
    (gA p M H hj 𝔛 A hρ) hgA₁ hgA₂ (bc p M H hj A) hbc₁ hbc₂ hθγG 𝔯₀ h𝔯₀def 𝔯₁ h𝔯₁def
  have hcover := cover_of_prime_over p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG
    (gA p M H hj 𝔛 A hρ) hgA₁ hgA₂ (bc p M H hj A) hbc₁ hbc₂ hθγG 𝔯₀ h𝔯₀def 𝔯₁ h𝔯₁def
  have hb : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = 𝔯₀ ⊓ 𝔯₁ :=
    (BranchReadE2.inf_le_of_forall_prime_le 𝔯₀ 𝔯₁ _ hrad hcover hN0 hN1).symm

  obtain ⟨hnc₀₁, hnc₁₀⟩ := not_le_branch_primes p M H hpM hpM2 hHp hj 𝔛 A hA hρ θ hwgen γ hγ n χκ ht Rg hgauss hres hγG
    (gA p M H hj 𝔛 A hρ) hgA₁ hgA₂ (bc p M H hj A) hbc₁ hbc₂ hθγG 𝔯₀ h𝔯₀def 𝔯₁ h𝔯₁def

  have hincl : (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom := RingHom.ext fun _ => rfl
  have hmin₀ : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯₀)).comp
      (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) := by
    rw [hincl, ← Ideal.map_map]
    exact BranchReadE2.map_maximalIdeal_localization_eq 𝔯₀ 𝔯₁ _ hb hnc₁₀
  have hmin₁ : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯₁)).comp
      (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₁) := by
    rw [hincl, ← Ideal.map_map]
    exact BranchReadE2.map_maximalIdeal_localization_eq 𝔯₁ 𝔯₀ _ (hb.trans (inf_comm 𝔯₀ 𝔯₁)) hnc₀₁

  have hV := ModularCurve.XHDRModelAtP.hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
    p M H hpM hpM2 hHp hj 𝔛 A hA (algebraMap (R p) ↥A) hρ rfl θ hwgen γ hγ hγinj n 𝔔 χκ hker hχA ht
  have h1𝔔 : (1 : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ∉ 𝔔 := fun h1 => h𝔔.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hleQ : ∀ (φ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) → ↥(xHFunctionFieldBar M H)) (hφG : ∀ t, φ t ∈ Rg.integers)
      (hval : ∀ t, ∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
        ((φ t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
        ∀ g : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
          ∃ v : Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)), v.HasValue g (χκ t / χκ 1))
      (t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))), (⟨φ t, hφG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers → t ∈ 𝔔 := by
    intro φ hφG hval t ht0

    obtain ⟨x, y, hy, hxy⟩ := (hgauss (φ t)).mp (hφG t)
    obtain ⟨x', y', hx', hy', hy'0, hfxy'⟩ :=
      ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (φ t) x y hy hxy
    obtain ⟨hyO, hyres⟩ := hres y' hy'
    obtain ⟨hxO, hxres⟩ := hres x' hx'
    have hmul : (⟨φ t, hφG t⟩ : ↥Rg.integers) * ⟨⟨coeffMap A.subtype y', hy'⟩, hyO⟩ = ⟨⟨coeffMap A.subtype x', hx'⟩, hxO⟩ := by
      apply Subtype.ext; apply Subtype.ext; simpa using hfxy'
    have hg : ((Rg.residue ⟨φ t, hφG t⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' =
        coeffMap (IsLocalRing.residue ↥A) x' := by
      have h := congrArg (fun z => ((Rg.residue z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A))) hmul
      simp only [map_mul] at h
      rw [← hyres, ← hxres]
      simpa using h
    obtain ⟨v, hv⟩ := hval t x' y' hy'0 hfxy' _ hg

    have hz : Rg.residue ⟨φ t, hφG t⟩ = 0 := by
      rw [← RingHom.mem_ker, Rg.ker_residue]; exact ht0
    rw [hz] at hv
    have := eq_zero_of_hasValue_zero v _ hv
    rw [map_one, div_one] at this
    rw [← hker, RingHom.mem_ker]
    exact this
  have hle₀ : 𝔯₀ ≤ 𝔔 := fun t ht => hleQ (fun t => γ t) hγG
    (fun t x y hy hxy g hg => ⟨_, (hV (γ t) t 1 h1𝔔 (by rw [map_one, mul_one])).1 x y hy hxy g hg⟩) t ((h𝔯₀def t).mp ht)
  have hle₁ : 𝔯₁ ≤ 𝔔 := fun t ht => hleQ (fun t => θ (γ t)) hθγG
    (fun t x y hy hxy g hg => ⟨_, (hV (γ t) t 1 h1𝔔 (by rw [map_one, mul_one])).2 x y hy hxy g hg⟩) t ((h𝔯₁def t).mp ht)

  haveI : Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj) := finiteType_chartAlgFin p M H hj
  haveI : Module.Flat (R p) ↥(chartAlgFin p (ΓM M H) hj) := (ModularCurve.XHDRLevel.flat_chartAlgFin_and_flat_chartAlgInf p (ΓM M H) hj).1
  have hpW₁ : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p : AlgebraicClosure ℚ)) ∈ W₁.nonunits := by
    rw [mem_nonunits_comap_iff]
    show θ (algebraMap _ _ (p : AlgebraicClosure ℚ)) ∈ Rg.integers.nonunits
    rw [AlgEquiv.commutes]
    exact natCast_mem_nonunits_integers p A Rg
  have hc₁ : ∀ h : ↥(xHFunctionFieldBar M H), (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ h * γ c = γ a) ↔
      (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) := by
    intro h
    rw [← hgauss]
    constructor
    · rintro ⟨a, c, hc, hfac⟩
      exact mem_of_fraction W₁ γ hγW 𝔯₁ h𝔯₁def' h a c hc hfac
    · intro hh
      exact ModularCurve.XHDRLevel.exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
        p M H hpM A hA (algebraMap (R p) ↥A) hρ rfl ↥(chartAlgFin p (ΓM M H) hj) W₁ γ hγW hγinj hγfrac hγA hWA₁ hW𝔪₁ hpW₁ 𝔯₁ h𝔯₁def' hmin₁ h hh
  exact ⟨𝔯₁, h𝔯₁p, hle₀, hle₁, hnc₀₁, hnc₁₀, hb, hc₁, hmin₀⟩

end H3
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

end BranchReadSkel
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
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

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔔 : 𝔔.IsPrime) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), γ t ∈ Rg.integers)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), s ≠ 0 ∧ e * γ s = γ a)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    [h𝔯₀p : 𝔯₀.IsPrime] :
    ∃ 𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), 𝔯₁.IsPrime ∧ 𝔯₀ ≤ 𝔔 ∧ 𝔯₁ ≤ 𝔔 ∧ ¬ 𝔯₀ ≤ 𝔯₁ ∧ ¬ 𝔯₁ ≤ 𝔯₀ ∧
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = 𝔯₀ ⊓ 𝔯₁ ∧
      (∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)) ∧
      (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯₀)).comp
          (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) =
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) :=
  BranchReadSkel.exists_snd_branch_min p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg θ hwgen γ hγ n 𝔔 h𝔔 χκ hker hχA ht Rg hgauss hres hγG hγinj hγfrac 𝔯₀ h𝔯₀def

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.BranchReadSkel"

end S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation (solution)
