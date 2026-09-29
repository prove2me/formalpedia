-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.exists_toSpec_comp_eq_and_isProper_and_twoAffineOpenCover_and_sections_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/82f2ec7a-2b22-5798-a0f9-6bf9cee5a6fa

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoAffineOpenCover_mem_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_exists_toSpec_comp_eq_and_isProper_and_twoAffineOpenCover_and_sections_of_surjective
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry ModularCurve NeronModelInfra MazurRapoportAppendix"
open scoped BigOperators

noncomputable section

namespace E5W2aCov

open AlgebraicCurve

private theorem appTop_subschemeι_eq_zero {Y : Scheme.{0}} (B : Y.IdealSheafData) (s : Γ(Y, ⊤))
    (hs : ∀ U : Y.affineOpens, Y.presheaf.map (homOfLE le_top).op s ∈ B.ideal U) :
    B.subschemeι.appTop s = 0 := by
  apply TopCat.Presheaf.section_ext B.subscheme.sheaf
  intro x hx
  obtain ⟨U, hxU⟩ : ∃ U : Y.affineOpens, B.subschemeι.base x ∈ (U : Y.Opens) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (B.subschemeι.base x)) isOpen_univ
    exact ⟨⟨U, hU⟩, hx⟩
  have hxV : x ∈ B.subschemeι ⁻¹ᵁ (U : Y.Opens) := hxU
  simp only [map_zero]
  have key : B.subscheme.presheaf.map (homOfLE (le_top : B.subschemeι ⁻¹ᵁ (U : Y.Opens) ≤ ⊤)).op
      (B.subschemeι.appTop s) = 0 := by
    have hnat := B.subschemeι.naturality (homOfLE (le_top : (U : Y.Opens) ≤ ⊤)).op
    have := congrArg (fun φ => φ.hom s) hnat
    simp only [CommRingCat.comp_apply] at this
    rw [Scheme.Hom.appTop]
    erw [← this]
    have hk : Y.presheaf.map (homOfLE le_top).op s ∈ RingHom.ker (B.subschemeι.app U).hom := by
      rw [B.ker_subschemeι_app U]; exact hs U
    exact hk
  have e1 := TopCat.Presheaf.germ_res_apply B.subscheme.presheaf
    (homOfLE (le_top : B.subschemeι ⁻¹ᵁ (U : Y.Opens) ≤ ⊤)) x hxV (B.subschemeι.appTop s)
  rw [key] at e1
  simp only [map_zero] at e1
  refine e1.symm.trans ?_
  exact (map_zero _).symm

private theorem exists_toSpec_of_surjective
    {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] (toκ : O →+* κ) (htoκ : Function.Surjective toκ)
    {Y : Scheme.{0}} (toBase : Y ⟶ Spec (CommRingCat.of O)) (B : Y.IdealSheafData)
    (hp : ∀ U : Y.affineOpens, ((p : ℕ) : Γ(Y, U)) ∈ B.ideal U) :
    ∃ yB : B.subscheme ⟶ Spec (CommRingCat.of κ), yB ≫ Spec.map (CommRingCat.ofHom toκ) = B.subschemeι ≫ toBase := by
  let f := B.subschemeι ≫ toBase
  let φ : O →+* Γ(B.subscheme, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hφp : φ (p : O) = 0 := by
    show f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (p : O)) = 0
    rw [map_natCast, map_natCast]
    have : (p : Γ(B.subscheme, ⊤)) = B.subschemeι.appTop (p : Γ(Y, ⊤)) := by rw [map_natCast]
    rw [this]
    exact appTop_subschemeι_eq_zero B _ (fun U => by rw [map_natCast]; exact hp U)
  have hker : RingHom.ker toκ ≤ RingHom.ker φ := by
    rw [IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective toκ htoκ), hϖ, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hφp
  let ψ : κ →+* Γ(B.subscheme, ⊤) := RingHom.liftOfSurjective toκ htoκ ⟨φ, hker⟩
  have hψ : ψ.comp toκ = φ := RingHom.liftOfSurjective_comp toκ htoκ ⟨φ, hker⟩
  refine ⟨B.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
  have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom toκ) = Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← hψ]; rfl
  have h2 : Spec.map (CommRingCat.ofHom φ) =
      Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv := by
    rw [← Spec.map_comp]; rfl
  rw [Category.assoc]
  erw [h1]
  rw [h2, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

private theorem natCast_mem_comp_ideal
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (w : X0MqComponents R.width) (U : R.Y.affineOpens) :
    ((p : ℕ) : Γ(R.Y, U)) ∈ (R.comp w).ideal U := by
  classical
  have hprod : ∀ s : Finset (X0MqComponents R.width),
      (∏ v ∈ s, R.comp v).ideal U = ∏ v ∈ s, (R.comp v).ideal U := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.ideal_top,
        Pi.top_apply, Ideal.one_eq_top]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.ideal_mul,
        Pi.mul_apply, ih]
  have h := R.comp_prod U
  rw [hprod] at h
  have hle : ∏ v ∈ Finset.univ, (R.comp v).ideal U ≤ (R.comp w).ideal U :=
    (Ideal.prod_le_inf).trans (Finset.inf_le (Finset.mem_univ w))
  exact hle (h ▸ Ideal.mem_span_singleton_self _)

private theorem isIso_fst_and_fst_comp_eq_snd
    {O κ : Type} [CommRing O] [Field κ] (toκ : O →+* κ) (htoκ : Function.Surjective toκ)
    {Bs : Scheme.{0}} (yB : Bs ⟶ Spec (CommRingCat.of κ)) (g : Bs ⟶ Spec (CommRingCat.of O))
    (hg : yB ≫ Spec.map (CommRingCat.ofHom toκ) = g) :
    IsIso (pullback.fst g (Spec.map (CommRingCat.ofHom toκ))) ∧
      pullback.fst g (Spec.map (CommRingCat.ofHom toκ)) ≫ yB = pullback.snd g (Spec.map (CommRingCat.ofHom toκ)) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom toκ)) := IsClosedImmersion.spec_of_surjective _ htoκ
  have h2 : pullback.fst g (Spec.map (CommRingCat.ofHom toκ)) ≫ yB = pullback.snd g (Spec.map (CommRingCat.ofHom toκ)) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom toκ)), Category.assoc, hg, pullback.condition]
  refine ⟨⟨⟨pullback.lift (𝟙 _) yB (by rw [Category.id_comp, hg]), ?_, pullback.lift_fst _ _ _⟩⟩, h2⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, Category.id_comp, h2]

private theorem exists_iso_curveModel_of_strict
    {O κ : Type} [CommRing O] [Field κ] (toκ : O →+* κ) (htoκ : Function.Surjective toκ)
    {Bs : Scheme.{0}} (yB : Bs ⟶ Spec (CommRingCat.of κ)) (g : Bs ⟶ Spec (CommRingCat.of O))
    (hg : yB ≫ Spec.map (CommRingCat.ofHom toκ) = g)
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F)
    (e : pullback g (Spec.map (CommRingCat.ofHom toκ)) ⟶ M.C) [IsIso e] (he : e ≫ M.toBase = pullback.snd _ _) :
    ∃ φ : Bs ≅ M.C, φ.hom ≫ M.toBase = yB := by
  obtain ⟨hfst, hyB⟩ := isIso_fst_and_fst_comp_eq_snd toκ htoκ yB g hg
  haveI := hfst
  refine ⟨(asIso (pullback.fst g (Spec.map (CommRingCat.ofHom toκ)))).symm ≪≫ asIso e, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc, he, IsIso.inv_comp_eq, hyB]

private theorem exists_curveModel_iso
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (htoκ : Function.Surjective toκ)
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ) (c : X0MqComponents R.width)
    (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of κ))
    (hy : y ≫ Spec.map (CommRingCat.ofHom toκ) = (R.comp c).subschemeι ≫ R.toBase) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra κ F) (M : CurveModel κ F) (φ : (R.comp c).subscheme ≅ M.C),
      φ.hom ≫ M.toBase = y := by
  rcases c with b | ⟨n, i⟩
  ·
    obtain ⟨e, he, heb, -⟩ := R.strict_iso b
    haveI := he
    refine ⟨_, inferInstance, inferInstance, 𝔓.Mfib κ (toκ.comp ρO),
      exists_iso_curveModel_of_strict toκ htoκ y _ hy (𝔓.Mfib κ (toκ.comp ρO)) (e ≫ inv (𝔓.efib κ (toκ.comp ρO))) ?_⟩
    rw [Category.assoc, ← 𝔓.hefib κ (toκ.comp ρO), IsIso.inv_hom_id_assoc]
    exact heb
  ·
    obtain ⟨M, e, he, heb⟩ := R.exc_rational n i
    haveI := he
    refine ⟨RatFunc κ, inferInstance, inferInstance, M, exists_iso_curveModel_of_strict toκ htoκ y _ hy M (inv e) ?_⟩
    rw [IsIso.inv_comp_eq, heb]

private theorem smoothOfRelativeDimension_one_of_iso' {S X Y : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

private theorem exists_section_mem_range_of_iso_curveModel
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] {C : Scheme.{0}} (y : C ⟶ Spec (CommRingCat.of κ))
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F) (φ : C ≅ M.C) (hφ : φ.hom ≫ M.toBase = y)
    (x : C) (Z : Set C) (hZ : IsClosed Z) (hxZ : x ∈ Z) (hZne : Z ≠ Set.univ) :
    ∃ s : Spec (CommRingCat.of κ) ⟶ C, s ≫ y = 𝟙 _ ∧ x ∈ Set.range s.base := by
  have hy : y = φ.hom ≫ M.toBase := hφ.symm
  haveI : IsIntegral C := IsIntegral.of_isIso φ.inv
  haveI : SmoothOfRelativeDimension 1 y := smoothOfRelativeDimension_one_of_iso' (f := M.toBase) φ.symm hφ
  haveI : LocallyOfFiniteType y := by rw [hy]; infer_instance
  have hx : x ≠ genericPoint C := by
    rintro rfl
    apply hZne
    rw [Set.eq_univ_iff_forall]
    intro z
    exact hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 hxZ) ((genericPoint_specializes z).mem_closure)
  have hcl : IsClosed ({x} : Set C) := isClosed_singleton_of_ne_genericPoint y x hx
  obtain ⟨z, hz⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ y x hcl
  exact ⟨z.left, Over.w z, ⟨_, hz⟩⟩

private theorem singleton_ne_univ_of_iso_curveModel
    (κ : Type) [Field κ] {C : Scheme.{0}}
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F) (φ : C ≅ M.C) (x : C) :
    ({x} : Set C) ≠ Set.univ := by
  have hinf : Infinite M.C := by
    have h := (AlgebraicCurve.infinite_setOf_isClosed_singleton M.toBase).mono (Set.subset_univ _)
    exact Set.infinite_univ_iff.mp h
  haveI : Infinite C :=
    Infinite.of_injective (Scheme.homeoOfIso φ).symm (Scheme.homeoOfIso φ).symm.injective
  intro h
  exact Set.infinite_univ (h ▸ Set.finite_singleton x)

private theorem eta_mem_support_and_not_mem
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w) :
    R.η w ∈ (R.comp w).support ∧ R.η w ∉ (R.comp v).support := by
  obtain ⟨U, hU, hmax, hoth⟩ := R.η_stalk w
  constructor
  · rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff]
    intro f hf hbo
    have hunit : IsUnit (R.Y.presheaf.germ (U : R.Y.Opens) (R.η w) hU f) := (R.Y.mem_basicOpen f (R.η w) hU).1 hbo
    have hmem : (R.Y.presheaf.germ (U : R.Y.Opens) (R.η w) hU).hom f ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hmax]; exact Ideal.mem_map_of_mem _ hf
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem hunit
  · rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff]
    intro h
    have hle : Ideal.map (R.Y.presheaf.germ (U : R.Y.Opens) (R.η w) hU).hom ((R.comp v).ideal U) ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => h f hf ((R.Y.mem_basicOpen f (R.η w) hU).2 hu)
    rw [hoth v hvw, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle

private theorem exists_section_of_mem_support_of_ne
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w)
    (y : (R.comp w).subscheme ⟶ Spec (CommRingCat.of κ))
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F) (φ : (R.comp w).subscheme ≅ M.C) (hφ : φ.hom ≫ M.toBase = y)
    (q : R.Y) (hv : q ∈ (R.comp v).support) (hw : q ∈ (R.comp w).support) :
    ∃ s : Spec (CommRingCat.of κ) ⟶ (R.comp w).subscheme, s ≫ y = 𝟙 _ ∧ q ∈ Set.range (s ≫ (R.comp w).subschemeι).base := by
  obtain ⟨x, hx⟩ : q ∈ Set.range (R.comp w).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hw
  let Z : Set (R.comp w).subscheme := (R.comp w).subschemeι.base ⁻¹' ((R.comp v).support : Set R.Y)
  have hZ : IsClosed Z := (R.comp v).support.isClosed.preimage (R.comp w).subschemeι.base.hom.continuous
  have hxZ : x ∈ Z := by show (R.comp w).subschemeι.base x ∈ ((R.comp v).support : Set R.Y); rw [hx]; exact hv
  obtain ⟨hηw, hηv⟩ := eta_mem_support_and_not_mem R v w hvw
  have hZne : Z ≠ Set.univ := by
    obtain ⟨e, he⟩ : R.η w ∈ Set.range (R.comp w).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hηw
    intro hZu
    have : e ∈ Z := by rw [hZu]; exact Set.mem_univ e
    apply hηv
    have he' : (R.comp w).subschemeι.base e ∈ ((R.comp v).support : Set R.Y) := this
    rwa [he] at he'
  obtain ⟨s, hs, ⟨pt, hpt⟩⟩ := exists_section_mem_range_of_iso_curveModel κ y M φ hφ x Z hZ hxZ hZne
  refine ⟨s, hs, ⟨pt, ?_⟩⟩
  show (R.comp w).subschemeι.base (s.base pt) = _
  rw [hpt, hx]

private theorem chainPos_ne_chainPos_succ {node : Type} (width : node → ℕ) (n : node) (d : ℕ) (hd : d < width n) :
    DRResolvedModelPackageLevel.chainPos width n d ≠ DRResolvedModelPackageLevel.chainPos width n (d + 1) := by
  unfold DRResolvedModelPackageLevel.chainPos
  have h1 : d + 1 ≠ 0 := Nat.succ_ne_zero d
  by_cases h0 : d = 0
  · subst h0
    simp only [↓reduceDIte, h1]
    split_ifs <;> simp
  · simp only [h0, ↓reduceDIte, hd, h1]
    split_ifs with h2
    · intro h
      simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, Fin.mk.injEq, true_and] at h
      omega
    · simp

private theorem exists_section_edgePt'
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (c : X0MqComponents R.width)
    (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of κ))
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F) (φ : (R.comp c).subscheme ≅ M.C) (hφ : φ.hom ≫ M.toBase = y)
    (n : R.node) (d : Fin (R.width n)) (hc : R.edgePt n d ∈ (R.comp c).support) :
    ∃ s : Spec (CommRingCat.of κ) ⟶ (R.comp c).subscheme,
      s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base := by
  have hmem := R.edgePt_mem n d
  have hne := chainPos_ne_chainPos_succ R.width n d d.2
  by_cases hca : c = DRResolvedModelPackageLevel.chainPos R.width n d
  · refine exists_section_of_mem_support_of_ne R (DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) c ?_ y M φ hφ
      _ hmem.2 hc
    rw [hca]; exact hne.symm
  · exact exists_section_of_mem_support_of_ne R (DRResolvedModelPackageLevel.chainPos R.width n d) c (Ne.symm hca) y M φ hφ
      _ hmem.1 hc

private theorem exists_section_of_section
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] [IsLocalRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (c : X0MqComponents R.width)
    (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of κ))
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F) (φ : (R.comp c).subscheme ≅ M.C) (hφ : φ.hom ≫ M.toBase = y)
    (σ : Spec (CommRingCat.of O) ⟶ R.Y) (hσ : σ ≫ R.toBase = 𝟙 _)
    (hc : σ.base (IsLocalRing.closedPoint O) ∈ (R.comp c).support) :
    ∃ s : Spec (CommRingCat.of κ) ⟶ (R.comp c).subscheme,
      s ≫ y = 𝟙 _ ∧ σ.base (IsLocalRing.closedPoint O) ∈ Set.range (s ≫ (R.comp c).subschemeι).base := by
  set q := σ.base (IsLocalRing.closedPoint O) with hq
  obtain ⟨x, hx⟩ : q ∈ Set.range (R.comp c).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hc

  haveI : IsClosedImmersion (σ ≫ R.toBase) := by rw [hσ]; infer_instance
  haveI : IsClosedImmersion σ := IsClosedImmersion.of_comp σ R.toBase
  have hqcl : IsClosed ({q} : Set R.Y) := by
    have h := σ.isClosedEmbedding.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint O)

    convert h using 1
    apply Set.Subset.antisymm
    · rintro z (rfl : z = q)
      exact ⟨IsLocalRing.closedPoint O, rfl, rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      show σ.base t = σ.base (IsLocalRing.closedPoint O)
      exact congrArg _ (ht : t = IsLocalRing.closedPoint O)
  have hxcl : IsClosed ({x} : Set (R.comp c).subscheme) := by
    have hpre : (R.comp c).subschemeι.base ⁻¹' ({q} : Set R.Y) = {x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact (R.comp c).subschemeι.isClosedEmbedding.injective (hz.trans hx.symm)
      · rintro rfl; exact hx
    rw [← hpre]
    exact hqcl.preimage (R.comp c).subschemeι.base.hom.continuous
  obtain ⟨s, hs, ⟨pt, hpt⟩⟩ := exists_section_mem_range_of_iso_curveModel κ y M φ hφ x {x} hxcl rfl
    (singleton_ne_univ_of_iso_curveModel κ M φ x)
  refine ⟨s, hs, ⟨pt, ?_⟩⟩
  show (R.comp c).subschemeι.base (s.base pt) = _
  rw [hpt, hx]

private theorem nonempty_twoAffineOpenCover_of_iso_curveModel
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] {C : Scheme.{0}} (y : C ⟶ Spec (CommRingCat.of κ))
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F) (φ : C ≅ M.C) (hφ : φ.hom ≫ M.toBase = y) :
    Nonempty C.TwoAffineOpenCover := by
  haveI : GeometricallyReduced M.toBase := GeometricallyReduced.of_isReduced_of_perfectField M.toBase
  haveI : GeometricallyIrreducible M.toBase := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed M.toBase
  haveI : GeometricallyIntegral M.toBase :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible M.toBase
  obtain ⟨𝒱', -⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed κ M.toBase (genericPoint M.C)
  obtain ⟨𝒱, -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y M.toBase φ hφ 𝒱'
    (𝟙_ M.C.Modules) ((Scheme.Modules.pullback φ.hom).obj (𝟙_ M.C.Modules)) (Iso.refl _)
  exact ⟨𝒱⟩

end E5W2aCov

end

open E5W2aCov in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] [IsLocalRing O] {ρO : DRLevel.R p →+* O} (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (htoκ : Function.Surjective toκ)
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ) (c : X0MqComponents R.width) :
    ∃ y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of κ),
      y ≫ Spec.map (CommRingCat.ofHom toκ) = (R.comp c).subschemeι ≫ R.toBase ∧
      IsProper y ∧ Nonempty (((R.comp c).subscheme).TwoAffineOpenCover) ∧
      (∀ (n : R.node) (d : Fin (R.width n)), R.edgePt n d ∈ (R.comp c).support →
        ∃ s : Spec (CommRingCat.of κ) ⟶ (R.comp c).subscheme,
          s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base) ∧
      (∀ σ : Spec (CommRingCat.of O) ⟶ R.Y, σ ≫ R.toBase = 𝟙 _ →
        σ.base (IsLocalRing.closedPoint O) ∈ (R.comp c).support →
        ∃ s : Spec (CommRingCat.of κ) ⟶ (R.comp c).subscheme,
          s ≫ y = 𝟙 _ ∧ σ.base (IsLocalRing.closedPoint O) ∈ Set.range (s ≫ (R.comp c).subschemeι).base) := by
  obtain ⟨y, hy⟩ := exists_toSpec_of_surjective hϖ toκ htoκ R.toBase (R.comp c) (natCast_mem_comp_ideal R c)
  obtain ⟨F, _, _, M, φ, hφ⟩ := exists_curveModel_iso htoκ R c y hy
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom toκ)) := IsClosedImmersion.spec_of_surjective _ htoκ
  haveI : IsProper (y ≫ Spec.map (CommRingCat.ofHom toκ)) := by rw [hy]; infer_instance
  refine ⟨y, hy, IsProper.of_comp y (Spec.map (CommRingCat.ofHom toκ)),
    nonempty_twoAffineOpenCover_of_iso_curveModel κ y M φ hφ, ?_, ?_⟩
  · intro n d hnd
    exact exists_section_edgePt' R c y M φ hφ n d hnd
  · intro σ hσ hσc
    exact exists_section_of_section R c y M φ hφ σ hσ hσc

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_exists_toSpec_comp_eq_and_isProper_and_twoAffineOpenCover_and_sections_of_surjective
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_exists_toSpec_comp_eq_and_isProper_and_twoAffineOpenCover_and_sections_of_surjective (solution)
