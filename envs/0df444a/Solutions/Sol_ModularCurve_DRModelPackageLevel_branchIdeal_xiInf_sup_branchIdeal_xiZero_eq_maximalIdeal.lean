-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d4a6d34a-582f-5846-9465-1d94909faee6

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_ModularCurve_DRModelPackageLevel_xiInf_ne_xiZero
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ModularCurve_DRModelPackageLevel_xi_mem_preimage_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

section Unit1

noncomputable section

namespace ECL_TransvPlumb

private theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

private theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

section Engine
variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

private theorem not_surjective_of_crossing
    (f : ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) → ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) :
    ¬ Function.Surjective f := by
  intro hf
  haveI := 𝔛.isIntegral_fibre0 toκ
  haveI := 𝔛.smoothOfRelativeDimension_one_fibre0 toκ
  haveI : Infinite ↥(DRLevel.fibre0 (N₀ := N₀) toκ) := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
    exact Set.infinite_univ_iff.mp (h.mono (Set.subset_univ _))
  haveI : Infinite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) := Infinite.of_surjective f hf
  haveI : Finite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) := 𝔛.finite_crossings toκ
  exact not_finite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1))

private theorem comp0_genericPoint_notMem_range_comp1 [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (𝔛.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range ⇑(𝔛.comp κ toκ 1).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion κ toκ 1
  not_surjective_of_crossing 𝔛 κ toκ _ (surjective_fst_of_mem_range _ _ h)

private theorem comp1_genericPoint_notMem_range_comp0 [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (𝔛.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range ⇑(𝔛.comp κ toκ 0).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion κ toκ 0
  not_surjective_of_crossing 𝔛 κ toκ _ (surjective_snd_of_mem_range _ _ h)

private theorem eq_of_specializes_comp0_genericPoint [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]
    (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔛.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔛.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔛.comp_isClosedImmersion κ toκ 0
  haveI := 𝔛.comp_isClosedImmersion κ toκ 1
  rcases 𝔛.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔛.comp κ toκ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔛.comp κ toκ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp0_genericPoint_notMem_range_comp1 𝔛 κ toκ)

private theorem eq_of_specializes_comp1_genericPoint [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]
    (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔛.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔛.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔛.comp_isClosedImmersion κ toκ 0
  haveI := 𝔛.comp_isClosedImmersion κ toκ 1
  rcases 𝔛.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔛.comp κ toκ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp1_genericPoint_notMem_range_comp0 𝔛 κ toκ)
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔛.comp κ toκ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

section Local
variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

private def fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : DRLevel.R q →+* A) (τB : DRLevel.R q →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) : DRLevel.fibre (N₀ := N₀) τB ⟶ DRLevel.fibre (N₀ := N₀) τA :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

@[reassoc]
private theorem fibreMapOfComp_fst {A B : Type} [CommRing A] [CommRing B] (τA : DRLevel.R q →+* A) (τB : DRLevel.R q →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp (N₀ := N₀) τA τB φ h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [fibreMapOfComp, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
private theorem fibreMapOfComp_snd {A B : Type} [CommRing A] [CommRing B] (τA : DRLevel.R q →+* A) (τB : DRLevel.R q →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp (N₀ := N₀) τA τB φ h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

private theorem bcMap_eq_fibreMapOfComp {O : Type} [CommRing O] (ρO : DRLevel.R q →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ) :
    DRLevel.bcMap (N₀ := N₀) ρO toκ = fibreMapOfComp (N₀ := N₀) ρO (toκ.comp ρO) toκ rfl := by
  apply pullback.hom_ext
  · rw [fibreMapOfComp_fst, DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
  · rw [fibreMapOfComp_snd]; exact pullback.lift_snd _ _ _

private theorem fibreMapOfComp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (τA : DRLevel.R q →+* A) (τB : DRLevel.R q →+* B) (τC : DRLevel.R q →+* C)
    (φ : A →+* B) (hφ : φ.comp τA = τB) (ψ : B →+* C) (hψ : ψ.comp τB = τC)
    (χ : A →+* C) (hχ : χ.comp τA = τC) (e : ψ.comp φ = χ) :
    fibreMapOfComp (N₀ := N₀) τB τC ψ hψ ≫ fibreMapOfComp (N₀ := N₀) τA τB φ hφ =
      fibreMapOfComp (N₀ := N₀) τA τC χ hχ := by
  subst e
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreMapOfComp_fst]
  · simp only [Category.assoc, fibreMapOfComp_snd, fibreMapOfComp_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem isPullback_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : DRLevel.R q →+* A) (τB : DRLevel.R q →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    IsPullback (fibreMapOfComp (N₀ := N₀) τA τB φ h)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom τB)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom τA)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA) = Spec.map (CommRingCat.ofHom τB) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  have key : IsPullback (fibreMapOfComp (N₀ := N₀) τA τB φ h ≫ pullback.fst (DRLevel.toBase N₀ q) _)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom τB))) (DRLevel.toBase N₀ q)
      (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA)) := by
    rw [fibreMapOfComp_fst, hρι]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right key (fibreMapOfComp_snd (N₀ := N₀) τA τB φ h) (IsPullback.of_hasPullback _ _)

private theorem isClosedImmersion_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : DRLevel.R q →+* A)
    (τB : DRLevel.R q →+* B) (φ : A →+* B) (h : φ.comp τA = τB) (hφ : Function.Surjective φ) :
    IsClosedImmersion (fibreMapOfComp (N₀ := N₀) τA τB φ h) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφ
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp (N₀ := N₀) τA τB φ h).flip inferInstance

private theorem flat_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : DRLevel.R q →+* A)
    (τB : DRLevel.R q →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Flat (fibreMapOfComp (N₀ := N₀) τA τB φ h) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.toAlgebra
    show RingHom.Flat (algebraMap A B)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat A B)
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp (N₀ := N₀) τA τB φ h).flip inferInstance

private theorem surjective_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : DRLevel.R q →+* A)
    (τB : DRLevel.R q →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Surjective (fibreMapOfComp (N₀ := N₀) τA τB φ h) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp (N₀ := N₀) τA τB φ h).flip inferInstance

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ q] (toκ : O →+* κ)

include hϖ in

private theorem toκ_maximalIdeal (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

private def ι : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal hϖ toκ)

private theorem ι_comp : (ι hϖ toκ).comp ((IsLocalRing.residue O).comp ρO) = toκ.comp ρO :=
  RingHom.ext fun _ => rfl

private theorem bcMap_eq_comp :
    DRLevel.bcMap (N₀ := N₀) ρO toκ =
      fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ) ≫
        DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O) := by
  rw [bcMap_eq_fibreMapOfComp, bcMap_eq_fibreMapOfComp,
    fibreMapOfComp_comp (χ := toκ) (hχ := rfl) (e := RingHom.ext fun _ => rfl)]

include hϖ in

private theorem exists_bcMap_residue_eq (y : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hy : y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)).base y₀ = y := by
  set s := (DRLevel.XO.toBase (N₀ := N₀) ρO).base y with hs
  have hps : ((q : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  rw [bcMap_eq_fibreMapOfComp]
  obtain ⟨y₀, hy₀, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_fibreMapOfComp (N₀ := N₀) ρO ((IsLocalRing.residue O).comp ρO) (IsLocalRing.residue O) rfl) y
    (IsLocalRing.closedPoint _) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

end Local

section Stalks
variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]
  {O : Type} [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ q] (toκ : O →+* κ)

private theorem g_comp_j : (fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)) ≫ (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)) = DRLevel.bcMap (N₀ := N₀) ρO toκ := (bcMap_eq_comp ρO hϖ toκ).symm

private theorem flat_stalkMap_g (y : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO))) : (((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ))).stalkMap y).hom.Flat :=
  haveI := flat_fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)
  Flat.stalkMap _ y

private theorem stalkMap_j_surjective (x : ↥(DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO))) :
    Function.Surjective (((DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O))).stalkMap x) := by
  haveI : IsClosedImmersion (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)) := by
    rw [bcMap_eq_fibreMapOfComp]
    exact isClosedImmersion_fibreMapOfComp _ _ _ rfl Ideal.Quotient.mk_surjective
  exact ((DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O))).stalkMap_surjective x

private theorem stalkMap_bcMap_eq (y : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO))) :
    (DRLevel.bcMap (N₀ := N₀) ρO toκ).stalkMap y =
      ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkCongr
          (.of_eq (by rw [← Scheme.Hom.comp_apply, g_comp_j ρO hϖ toκ]))).hom ≫
        ((DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O))).stalkMap (((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ))).base y) ≫ ((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ))).stalkMap y := by
  rw [Scheme.Hom.stalkMap_congr_hom _ _ (g_comp_j ρO hϖ toκ).symm y, Scheme.Hom.stalkMap_comp]
  rfl

end Stalks

end ECL_TransvPlumb

end

end Unit1

section Unit2

set_option autoImplicit false

open IsLocalRing AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ECL_Transv

private theorem fromSpecStalk_comap_closedPoint_spec {X : Scheme} {x ξ : X} (h : ξ ⤳ x) :
    X.fromSpecStalk x (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom (closedPoint (X.presheaf.stalk ξ))) =
      ξ := by
  have e := congrArg (fun f : Spec (X.presheaf.stalk ξ) ⟶ X => f (closedPoint (X.presheaf.stalk ξ)))
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, Scheme.fromSpecStalk_closedPoint] using e

private theorem exists_specializes_and_eq_comap_stalkSpecializes {X : Scheme} (y : X)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    ∃ (z : X) (hz : z ⤳ y),
      𝔮 = Ideal.comap (X.presheaf.stalkSpecializes hz).hom (maximalIdeal (X.presheaf.stalk z)) := by
  let q : Spec (X.presheaf.stalk y) := ⟨𝔮, inferInstance⟩
  have hz : X.fromSpecStalk y q ⤳ y := by
    have hmem : X.fromSpecStalk y q ∈ Set.range (X.fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  refine ⟨X.fromSpecStalk y q, hz, ?_⟩
  have hinj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  have h1 := hinj (fromSpecStalk_comap_closedPoint_spec hz)
  exact (congrArg PrimeSpectrum.asIdeal h1).symm

private theorem comap_stalkSpecializes_refl_maximalIdeal {X : Scheme} (y : X) :
    Ideal.comap (X.presheaf.stalkSpecializes (specializes_refl y)).hom (maximalIdeal (X.presheaf.stalk y)) =
      maximalIdeal (X.presheaf.stalk y) := by
  simp

private theorem eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal {C X : Scheme} (i₁ i₂ : C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hsurj : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (η : C) (hη : ∀ c : C, c ≠ η → IsClosed ({c} : Set C)) {y : X} (h₁ : i₁.base η ⤳ y) (h₂ : i₂.base η ⤳ y)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂ := by
  obtain ⟨z, hz, rfl⟩ := exists_specializes_and_eq_comap_stalkSpecializes y 𝔮
  rcases hsurj z with ⟨c, hc⟩ | ⟨c, hc⟩
  · by_cases hcη : c = η
    · subst hcη
      subst hc
      exact Or.inr (Or.inl rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)
  · by_cases hcη : c = η
    · subst hcη
      subst hc
      exact Or.inr (Or.inr rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)

private theorem eq_of_branchIdeal_eq {X : Scheme} {x ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ x) (h₂ : ξ₂ ⤳ x)
    (h : Scheme.branchIdeal h₁ = Scheme.branchIdeal h₂) : ξ₁ = ξ₂ := by
  have hpt : PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) =
      PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    PrimeSpectrum.ext h
  rw [← fromSpecStalk_comap_closedPoint_spec h₁, ← fromSpecStalk_comap_closedPoint_spec h₂, hpt]

private theorem specializes_of_branchIdeal_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (hle : Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂) : ξ₁ ⤳ ξ₂ := by
  have hsp : (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) :
      Spec (X.presheaf.stalk y)) ⤳
        PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have := hsp.map (X.fromSpecStalk y).continuous
  rwa [fromSpecStalk_comap_closedPoint_spec h₁, fromSpecStalk_comap_closedPoint_spec h₂] at this

private theorem branchIdeal_ne_maximalIdeal_and_not_le {C X : Scheme} (i₁ i₂ : C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (η : C) (hη : ∀ c : C, c ≠ η → IsClosed ({c} : Set C)) {y : X} (h₁ : i₁.base η ⤳ y) (h₂ : i₂.base η ⤳ y)
    (hne : i₁.base η ≠ i₂.base η) (hy₁ : i₁.base η ≠ y) (hy₂ : i₂.base η ≠ y) :
    Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      Scheme.branchIdeal h₂ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      ¬ Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂ ∧ ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁ := by
  refine ⟨fun h => hy₁ ?_, fun h => hy₂ ?_, fun hle => ?_, fun hle => ?_⟩
  · exact eq_of_branchIdeal_eq h₁ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  · exact eq_of_branchIdeal_eq h₂ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  ·

    have hsp := specializes_of_branchIdeal_le h₁ h₂ hle
    obtain ⟨c, hc⟩ : i₂.base η ∈ Set.range i₁.base :=
      hsp.mem_closed i₁.isClosedEmbedding.isClosed_range ⟨η, rfl⟩
    by_cases hcη : c = η
    · exact hne (by rw [← hc, hcη])
    · have hcl : IsClosed ({i₂.base η} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη c hcη)
      exact hy₂ (h₂.mem_closed hcl (Set.mem_singleton _)).symm
  · have hsp := specializes_of_branchIdeal_le h₂ h₁ hle
    obtain ⟨c, hc⟩ : i₁.base η ∈ Set.range i₂.base :=
      hsp.mem_closed i₂.isClosedEmbedding.isClosed_range ⟨η, rfl⟩
    by_cases hcη : c = η
    · exact hne (by rw [← hc, hcη])
    · have hcl : IsClosed ({i₁.base η} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη c hcη)
      exact hy₁ (h₁.mem_closed hcl (Set.mem_singleton _)).symm

private theorem eq_branchIdeal_of_isPrime_of_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (htri : ∀ 𝔮 : Ideal (X.presheaf.stalk y), 𝔮.IsPrime →
      𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂)
    (hP : Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y))
    (hQP : ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁)
    (J : Ideal (X.presheaf.stalk y)) [hJp : J.IsPrime] (hJ : J ≤ Scheme.branchIdeal h₁) :
    J = Scheme.branchIdeal h₁ := by
  rcases htri J hJp with hm | hp | hq
  · subst hm
    exact absurd (le_antisymm (le_maximalIdeal (Scheme.branchIdeal_isPrime h₁).ne_top) hJ) hP
  · exact hp
  · subst hq
    exact absurd hJ hQP

section Frame

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (τ : DRLevel.R q →+* κ)

private theorem comp0_genericPoint_specializes [IsIntegral (DRLevel.fibre0 (N₀ := N₀) τ)]
    (n : ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1))) :
    (𝔛.comp κ τ 0).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) τ)) ⤳
      (𝔛.comp κ τ 0).base ((pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)).base n) :=
  (genericPoint_specializes _).map (𝔛.comp κ τ 0).continuous

private theorem comp1_snd_eq_comp0_fst (n : ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1))) :
    (𝔛.comp κ τ 1).base ((pullback.snd (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)).base n) =
      (𝔛.comp κ τ 0).base ((pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)).base n) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

private theorem comp1_genericPoint_specializes [IsIntegral (DRLevel.fibre0 (N₀ := N₀) τ)]
    (n : ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1))) :
    (𝔛.comp κ τ 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) τ)) ⤳
      (𝔛.comp κ τ 0).base ((pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)).base n) :=
  ((genericPoint_specializes _).map (𝔛.comp κ τ 1).continuous).trans
    (specializes_of_eq (comp1_snd_eq_comp0_fst 𝔛 κ τ n))

private theorem frame_eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal [IsIntegral (DRLevel.fibre0 (N₀ := N₀) τ)]
    (n : ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)))
    (𝔮 : Ideal ((DRLevel.fibre (N₀ := N₀) τ).presheaf.stalk
      ((𝔛.comp κ τ 0).base ((pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)).base n)))) [𝔮.IsPrime] :
    𝔮 = maximalIdeal _ ∨ 𝔮 = Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 κ τ n) ∨
      𝔮 = Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 κ τ n) :=
  haveI := 𝔛.comp_isClosedImmersion κ τ 0
  haveI := 𝔛.comp_isClosedImmersion κ τ 1
  haveI := 𝔛.smoothOfRelativeDimension_one_fibre0 τ
  eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal (𝔛.comp κ τ 0) (𝔛.comp κ τ 1) (𝔛.comp_jointly_surjective κ τ)
    (genericPoint (DRLevel.fibre0 (N₀ := N₀) τ))
    (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom τ))) c hc)
    (comp0_genericPoint_specializes 𝔛 κ τ n) (comp1_genericPoint_specializes 𝔛 κ τ n) 𝔮

private theorem frame_branchIdeal_ne_maximalIdeal_and_not_le
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (toκ : O →+* κ) [IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hy₁ : (𝔛.comp κ (toκ.comp ρO) 0).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) ≠
      (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n))
    (hy₂ : (𝔛.comp κ (toκ.comp ρO) 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) ≠
      (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)) :
    Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) ≠ maximalIdeal _ ∧
      Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) ≠ maximalIdeal _ ∧
      ¬ Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) ≤
          Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) ∧
      ¬ Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) ≤
          Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) :=
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 0
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 1
  haveI := 𝔛.smoothOfRelativeDimension_one_fibre0 (toκ.comp ρO)
  have hne : (𝔛.comp κ (toκ.comp ρO) 0).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) ≠
      (𝔛.comp κ (toκ.comp ρO) 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) := fun h =>
    ModularCurve.DRModelPackageLevel.xiInf_ne_xiZero N₀ q hqN 𝔛 O ρO hϖ κ toκ
      (by
        show (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base _ = (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base _
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  branchIdeal_ne_maximalIdeal_and_not_le (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))
    (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))) c hc)
    (comp0_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) (comp1_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n) hne hy₁ hy₂

omit [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] in

private theorem bcMap_comp_fst (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O) (toκ : O →+* κ) :
    DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
  rw [DRLevel.bcMap]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem comp0_genericPoint_ne_and_comp1_genericPoint_ne (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O) (toκ : O →+* κ)
    [IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) :
    (𝔛.comp κ (toκ.comp ρO) 0).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) ≠
        (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) ∧
      (𝔛.comp κ (toκ.comp ρO) 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) ≠
        (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) := by
  have hy : (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) ∈
        Set.range (𝔛.comp κ (toκ.comp ρO) 0).base ∧
      (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) ∈
        Set.range (𝔛.comp κ (toκ.comp ρO) 1).base :=
    ⟨⟨_, rfl⟩, ⟨(pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, comp1_snd_eq_comp0_fst 𝔛 κ (toκ.comp ρO) n⟩⟩
  have hsm := ModularCurve.DRModelPackageLevel.xi_mem_preimage_smoothLocus N₀ q hqN 𝔛 O ρO κ toκ
  have key : ∀ z : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)),
      (DRLevel.bcMap ρO toκ).base z ∈
          (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) ⁻¹ᵁ 𝔛.smoothLocus) →
        z ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    intro z hz
    rw [Scheme.Hom.mem_preimage] at hz ⊢
    rw [← bcMap_comp_fst κ O ρO toκ, Scheme.Hom.comp_apply]
    exact hz
  have h1 := key _ (by
    have := hsm.1
    rwa [show 𝔛.ξinf ρO toκ = (DRLevel.bcMap ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 0).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) from
      Scheme.Hom.comp_apply _ _ _] at this)
  have h2 := key _ (by
    have := hsm.2
    rwa [show 𝔛.ξzero ρO toκ = (DRLevel.bcMap ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) from
      Scheme.Hom.comp_apply _ _ _] at this)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter N₀ q hqN 𝔛 κ (toκ.comp ρO) _).mp h1
      (by rw [h]; exact hy)
  · exact (ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter N₀ q hqN 𝔛 κ (toκ.comp ρO) _).mp h2
      (by rw [h]; exact hy)

end Frame

end ECL_Transv

end Unit2

section Unit3

set_option autoImplicit false

open TensorProduct

private theorem eq_bot_of_forall_isPrime_le' {T : Type*} [CommRing T] [IsReduced T] {I : Ideal T}
    (h : ∀ 𝔮 : Ideal T, 𝔮.IsPrime → I ≤ 𝔮) : I = ⊥ := by
  refine le_bot_iff.mp ?_
  calc I ≤ sInf { J : Ideal T | J.IsPrime } := le_sInf fun 𝔮 h𝔮 => h 𝔮 h𝔮
    _ = nilradical T := (nilradical_eq_sInf T).symm
    _ = ⊥ := nilradical_eq_zero T

private theorem flat_quotient_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : Ideal A) : Module.Flat (A ⧸ P) (B ⧸ P.map (algebraMap A B)) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P).toLinearEquiv

private theorem isSMulRegular_quotient_map_of_notMem {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (P : Ideal A) [P.IsPrime] {a : A} (ha : a ∉ P) :
    IsSMulRegular (B ⧸ P.map (algebraMap A B)) (algebraMap A (B ⧸ P.map (algebraMap A B)) a) := by
  haveI := flat_quotient_map_of_flat (A := A) (B := B) P
  have hreg : IsSMulRegular (A ⧸ P) (Ideal.Quotient.mk P a) :=
    mul_right_injective₀ (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)
  have h := hreg.of_flat (S := B ⧸ P.map (algebraMap A B))
  rwa [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h

private theorem map_eq_of_flat_of_forall_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B}
    (h1 : P.map (algebraMap A B) ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap (algebraMap A B) ≤ P → 𝔭' ≤ 𝔮) :
    P.map (algebraMap A B) = 𝔭' := by
  refine le_antisymm h1 fun q hq => ?_
  let S : Submonoid B := P.primeCompl.map (algebraMap A B)

  have hbot : 𝔭'.map (algebraMap B (Localization S)) = ⊥ := by
    refine eq_bot_of_forall_isPrime_le' fun 𝔔 h𝔔 => ?_
    obtain ⟨hprime, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S (Localization S) 𝔔).mp h𝔔
    refine Ideal.map_le_iff_le_comap.mpr (h2 _ hprime fun a ha => ?_)
    by_contra ha'
    exact Set.disjoint_left.mp hdisj (Submonoid.mem_map_of_mem (algebraMap A B) (ha' : a ∈ P.primeCompl))
      ha
  have hq0 : algebraMap B (Localization S) q = 0 := by
    have : algebraMap B (Localization S) q ∈ 𝔭'.map (algebraMap B (Localization S)) :=
      Ideal.mem_map_of_mem _ hq
    simpa [hbot] using this
  obtain ⟨⟨s, hs⟩, hsq⟩ := (IsLocalization.map_eq_zero_iff S (Localization S) q).mp hq0
  obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hs

  have hreg := isSMulRegular_quotient_map_of_notMem (B := B) P (ha : a ∉ P)
  have hzero : algebraMap A (B ⧸ P.map (algebraMap A B)) a • Ideal.Quotient.mk _ q =
      algebraMap A (B ⧸ P.map (algebraMap A B)) a • (0 : B ⧸ P.map (algebraMap A B)) := by
    rw [smul_zero, smul_eq_mul, IsScalarTower.algebraMap_apply A B (B ⧸ P.map (algebraMap A B)),
      Ideal.Quotient.algebraMap_eq, ← map_mul]
    simpa using congrArg (Ideal.Quotient.mk (P.map (algebraMap A B))) hsq
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hreg hzero)

private theorem map_eq_of_flat_of_forall_le_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B} (h1 : P.map ψ ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap ψ ≤ P → 𝔭' ≤ 𝔮) : P.map ψ = 𝔭' := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact map_eq_of_flat_of_forall_le P h1 h2

end Unit3

section Unit4

set_option autoImplicit false

private theorem eq_under_of_le_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hle : q ≤ 𝔭'.under A) : q = 𝔭'.under A := by
  obtain ⟨𝔮, h𝔮le, h𝔮prime, h𝔮over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := 𝔭'.under A) 𝔭' hle
  rw [hmin 𝔮 h𝔮prime h𝔮le] at h𝔮over
  exact h𝔮over.over

private theorem eq_comap_of_le_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hle : q ≤ 𝔭'.comap ψ) : q = 𝔭'.comap ψ := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact eq_under_of_le_of_flat 𝔭' hmin hle

private theorem not_le_comap_of_ne_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hne : q ≠ 𝔭'.comap ψ) : ¬ q ≤ 𝔭'.comap ψ :=
  fun hle => hne (eq_comap_of_le_of_flat_ringHom ψ hψ 𝔭' hmin hle)

end Unit4

section Unit5

set_option autoImplicit false

private theorem eq_of_isRadical_of_le_of_forall_le {B : Type*} [CommRing B] {I 𝔭 : Ideal B}
    (hI : I.IsRadical) [𝔭.IsPrime] (hle : I ≤ 𝔭)
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → I ≤ 𝔮 → 𝔭 ≤ 𝔮) : I = 𝔭 := by
  refine le_antisymm hle ?_
  rw [← Ideal.radical_eq_iff.mpr hI, Ideal.radical_eq_sInf]
  exact le_sInf fun 𝔮 h𝔮 => hmin 𝔮 h𝔮.2 h𝔮.1

private theorem le_of_map_le_map_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {I J : Ideal A}
    (h : I.map (algebraMap A B) ≤ J.map (algebraMap A B)) : I ≤ J := by
  calc I = (I.map (algebraMap A B)).comap (algebraMap A B) :=
        (Ideal.comap_map_eq_self_of_faithfullyFlat I).symm
    _ ≤ (J.map (algebraMap A B)).comap (algebraMap A B) := Ideal.comap_mono h
    _ = J := Ideal.comap_map_eq_self_of_faithfullyFlat J

private theorem le_of_map_le_map_of_flat_of_isLocalHom {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {I J : Ideal A}
    (h : I.map f ≤ J.map f) : I ≤ J := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact le_of_map_le_map_of_faithfullyFlat (A := A) (B := B) h

private theorem sup_eq_maximalIdeal_of_map_maximalIdeal_le {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {P Q : Ideal A}
    (hP : P ≠ ⊤) (hQ : Q ≠ ⊤)
    (h : (IsLocalRing.maximalIdeal A).map f ≤ (P ⊔ Q).map f) :
    P ⊔ Q = IsLocalRing.maximalIdeal A :=
  le_antisymm (sup_le (IsLocalRing.le_maximalIdeal hP) (IsLocalRing.le_maximalIdeal hQ))
    (le_of_map_le_map_of_flat_of_isLocalHom f hf h)

end Unit5

section Unit6

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

universe u

namespace TransvChair

variable {X Y : Scheme.{u}}

private theorem comap_stalkMap_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x) :
    ((maximalIdeal (X.presheaf.stalk ξ)).comap (X.presheaf.stalkSpecializes h).hom).comap
        (f.stalkMap x).hom =
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, ← Scheme.Hom.stalkSpecializes_stalkMap f ξ x h,
    CommRingCat.hom_comp, ← Ideal.comap_comap, maximalIdeal_comap]

private theorem ker_stalkMap_le_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x)
    [Nontrivial (X.presheaf.stalk ξ)] :
    RingHom.ker (f.stalkMap x).hom ≤
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  intro s hs
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.map (f.stalkMap ξ).hom
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply f ξ x h, RingHom.mem_ker.mp hs, map_zero] at hu'
  exact not_isUnit_zero hu'

private theorem stalkSpecializes_surjective_of_eq {x x' : X} (e : x' = x) :
    Function.Surjective (X.presheaf.stalkSpecializes (specializes_of_eq e)).hom := by
  subst e
  intro t
  refine ⟨t, ?_⟩
  have : X.presheaf.stalkSpecializes (specializes_of_eq (rfl : x' = x')) = 𝟙 _ :=
    X.presheaf.stalkSpecializes_refl x'
  rw [this]
  rfl

private theorem isRadical_of_specLift {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ X) (x : X)
    (K : Ideal (X.presheaf.stalk x)) [IsLocalRing ((X.presheaf.stalk x) ⧸ K)]
    [IsLocalHom (Ideal.Quotient.mk K)]
    (g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ Z)
    (hg : g ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
    (hpt : (g ≫ j).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x)
    (hK : K ≤ RingHom.ker ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        j.stalkMap (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K)))).hom) :
    K.IsRadical := by
  have claim : ∀ (f : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X)
      (_ : f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (hfpt : f.base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x) (a : X.presheaf.stalk x),
      (Scheme.stalkClosedPointTo f).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom a) =
        Ideal.Quotient.mk K a := by
    intro f hf hfpt a
    subst hf
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    have hqU : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x).base
        (closedPoint ((X.presheaf.stalk x) ⧸ K)) ∈ U := by
      rw [hfpt]
      exact hxU
    have e1 : (X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom
          ((X.presheaf.germ U x hxU).hom s) =
        (X.presheaf.germ U _ hqU).hom s := by
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [e1, ← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
    rfl
  rw [Ideal.isRadical_iff_quotient_reduced]
  refine ⟨fun r ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hb : (Scheme.stalkClosedPointTo g).hom
        ((j.stalkMap (g.base (closedPoint _))).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) =
      Ideal.Quotient.mk K a := by
    have := claim (g ≫ j) hg hpt a
    rw [Scheme.stalkClosedPointTo_comp] at this
    first | exact this | simpa only [CommRingCat.comp_apply] using this
  have ham : a ^ m ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact hm
  have hbm := hK ham
  rw [RingHom.mem_ker, map_pow, CommRingCat.hom_comp, RingHom.comp_apply] at hbm
  have hb0 := IsReduced.eq_zero _ ⟨m, hbm⟩
  rw [← hb]
  erw [hb0]
  exact map_zero _

private theorem isRadical_comap_ker_sup_comap_ker {C₁ C₂ : Scheme.{u}}
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced (pullback i₁ i₂)] (z : ↥(pullback i₁ i₂)) (x : X)
    (h₁ : i₁.base ((pullback.fst i₁ i₂).base z) = x)
    (h₂ : i₂.base ((pullback.snd i₁ i₂).base z) = x) :
    ((RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom).IsRadical := by

  let σ₁ : X.presheaf.stalk x →+* C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) :=
    (i₁.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom
  let σ₂ : X.presheaf.stalk x →+* C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) :=
    (i₂.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom
  have hσ₁ : Function.Surjective σ₁ :=
    (i₁.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₁)
  have hσ₂ : Function.Surjective σ₂ :=
    (i₂.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₂)
  have hK₁ : RingHom.ker σ₁ =
      (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom :=
    (RingHom.comap_ker _ _).symm
  have hK₂ : RingHom.ker σ₂ =
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom :=
    (RingHom.comap_ker _ _).symm
  set K := (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
    (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom with hKdef
  have hK₁le : RingHom.ker σ₁ ≤ K := hK₁ ▸ le_sup_left
  have hK₂le : RingHom.ker σ₂ ≤ K := hK₂ ▸ le_sup_right

  have hker₁ : RingHom.ker σ₁ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₁
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hker₂ : RingHom.ker σ₂ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₂
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hKmax : K ≤ maximalIdeal _ := sup_le (hK₁ ▸ hker₁) (hK₂ ▸ hker₂)
  have hKtop : K ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top (top_le_iff.mp (h ▸ hKmax))
  haveI : Nontrivial ((X.presheaf.stalk x) ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hKtop
  haveI : IsLocalRing ((X.presheaf.stalk x) ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk K) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let α₁ : C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₁le).comp (RingHom.quotientKerEquivOfSurjective hσ₁).symm.toRingHom
  let α₂ : C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₂le).comp (RingHom.quotientKerEquivOfSurjective hσ₂).symm.toRingHom
  have hα₁ : α₁.comp σ₁ = Ideal.Quotient.mk K := by
    ext a
    simp [α₁, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  have hα₂ : α₂.comp σ₂ = Ideal.Quotient.mk K := by
    ext a
    simp [α₂, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  haveI : IsLocalHom α₁ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₁) (by rw [← RingHom.coe_comp, hα₁]; exact Ideal.Quotient.mk_surjective))
  haveI : IsLocalHom α₂ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₂) (by rw [← RingHom.coe_comp, hα₂]; exact Ideal.Quotient.mk_surjective))

  let q : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x
  let a₁ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₁ :=
    Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _
  let a₂ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₂ :=
    Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _
  have hring₁ : (X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ i₁.stalkMap _ ≫ CommRingCat.ofHom α₁ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₁ (σ₁ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₁]
  have hring₂ : (X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫ i₂.stalkMap _ ≫ CommRingCat.ofHom α₂ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₂ (σ₂ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₂]
  have ha₁ : a₁ ≫ i₁ = q := by
    simp only [a₁, q, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₁)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₁]
    rfl
  have ha₂ : a₂ ≫ i₂ = q := by
    simp only [a₂, q, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₂)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₂]
    rfl
  let g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ pullback i₁ i₂ :=
    pullback.lift a₁ a₂ (ha₁.trans ha₂.symm)
  have hg : g ≫ (pullback.fst i₁ i₂ ≫ i₁) = q := by
    rw [← Category.assoc, pullback.lift_fst, ha₁]
  have hpt : (g ≫ (pullback.fst i₁ i₂ ≫ i₁)).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x := by
    rw [hg]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

  have hw₁ : (pullback.fst i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.fst i₁ i₂).base z := by
    change (g ≫ pullback.fst i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_fst]
    change (Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hw₂ : (pullback.snd i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.snd i₁ i₂).base z := by
    change (g ≫ pullback.snd i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_snd]
    change (Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  refine isRadical_of_specLift (pullback.fst i₁ i₂ ≫ i₁) x K g hg hpt (sup_le ?_ ?_)
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have e : (X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ X.presheaf.stalkSpecializes
          (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom a := by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [Scheme.Hom.stalkMap_comp]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) = 0
    rw [e]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₁ _ _ (specializes_of_eq hw₁), ha, map_zero,
      map_zero]
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have hcond : (pullback.fst i₁ i₂ ≫ i₁).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
        (pullback.snd i₁ i₂ ≫ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) :=
      congrArg (fun k => k.base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))))
        (pullback.condition (f := i₁) (g := i₂))
    rw [Scheme.Hom.stalkMap_congr_hom _ _ pullback.condition, Scheme.Hom.stalkMap_comp]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      (((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a)) = 0
    have e : ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫
          X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom a := by
      change ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          X.presheaf.stalkSpecializes (Inseparable.of_eq hcond).ge).hom a = _
      rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [e]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₂ _ _ (specializes_of_eq hw₂), ha, map_zero,
      map_zero]

private theorem branchIdeal_sup_eq_transport {x x' ζ₁ ζ₁' ζ₂ ζ₂' : X}
    (ex : x = x') (e₁ : ζ₁ = ζ₁') (e₂ : ζ₂ = ζ₂')
    (g₁ : ζ₁ ⤳ x) (g₂ : ζ₂ ⤳ x) (g₁' : ζ₁' ⤳ x') (g₂' : ζ₂' ⤳ x')
    (H : Scheme.branchIdeal g₁ ⊔ Scheme.branchIdeal g₂ = maximalIdeal (X.presheaf.stalk x)) :
    Scheme.branchIdeal g₁' ⊔ Scheme.branchIdeal g₂' = maximalIdeal (X.presheaf.stalk x') := by
  subst ex e₁ e₂
  exact H

private theorem descent {A Abar B : Type*} [CommRing A] [CommRing Abar] [CommRing B]
    [IsLocalRing A] [IsLocalRing Abar] [IsLocalRing B] [IsReduced B]
    (θ : A →+* Abar) (hθ : Function.Surjective θ) (ψ : Abar →+* B) (hψ : ψ.Flat) [IsLocalHom ψ]
    {P Q : Ideal A} {P' Q' : Ideal B} [P'.IsPrime] [Q'.IsPrime]
    (hP : P'.comap (ψ.comp θ) = P) (hQ : Q'.comap (ψ.comp θ) = Q) (hPQ : P ≠ Q)
    (htri : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 = maximalIdeal B ∨ 𝔮 = P' ∨ 𝔮 = Q')
    (hPm : P' ≠ maximalIdeal B) (hQm : Q' ≠ maximalIdeal B) (hPQ' : ¬ P' ≤ Q') (hQP' : ¬ Q' ≤ P')
    (hκ : P' ⊔ Q' = maximalIdeal B) :
    P ⊔ Q = maximalIdeal A := by
  haveI : IsLocalHom θ := IsLocalHom.of_surjective θ hθ

  have hminP : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ P' → 𝔮 = P' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hPm
    · rfl
    · exact absurd hle hQP'
  have hminQ : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ Q' → 𝔮 = Q' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hQm
    · exact absurd hle hPQ'
    · rfl

  have hkerP : RingHom.ker θ ≤ P := by
    intro a ha
    rw [← hP, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hkerQ : RingHom.ker θ ≤ Q := by
    intro a ha
    rw [← hQ, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hcmP : (P.map θ).comap θ = P := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerP]
  have hcmQ : (Q.map θ).comap θ = Q := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerQ]

  have hPbar : P'.comap ψ = P.map θ := by
    rw [← hP, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  have hQbar : Q'.comap ψ = Q.map θ := by
    rw [← hQ, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  haveI hPbp : (P.map θ).IsPrime := hPbar ▸ Ideal.comap_isPrime ψ P'
  haveI hQbp : (Q.map θ).IsPrime := hQbar ▸ Ideal.comap_isPrime ψ Q'
  have hPQbar : P.map θ ≠ Q.map θ := fun h => hPQ (by rw [← hcmP, h, hcmQ])

  have hmapP : (P.map θ).map ψ = P' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hPbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exact le_rfl
    · exfalso
      rw [hQbar] at hle
      rw [← hPbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ P' hminP hPQbar.symm hle
  have hmapQ : (Q.map θ).map ψ = Q' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hQbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exfalso
      rw [hPbar] at hle
      rw [← hQbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ Q' hminQ hPQbar hle
    · exact le_rfl

  have hbar : P.map θ ⊔ Q.map θ = maximalIdeal Abar := by
    refine sup_eq_maximalIdeal_of_map_maximalIdeal_le ψ hψ (Ideal.IsPrime.ne_top hPbp)
      (Ideal.IsPrime.ne_top hQbp) ?_
    rw [Ideal.map_sup, hmapP, hmapQ, hκ]
    exact Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap ψ).ge
  calc P ⊔ Q = ((P ⊔ Q).map θ).comap θ := by
        rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, eq_comm, sup_eq_left]
        exact hkerP.trans le_sup_left
    _ = maximalIdeal A := by rw [Ideal.map_sup, hbar, maximalIdeal_comap]

end TransvChair

end Unit6

section Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing ECL_TransvPlumb ECL_Transv

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) :
    Scheme.branchIdeal hinf ⊔ Scheme.branchIdeal hzero = IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) := by
  classical
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 0
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 1
  haveI := 𝔛.crossing_reduced κ (toκ.comp ρO)
  haveI : IsReduced (DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)) := 𝔛.fibre_reduced κ (toκ.comp ρO)

  have h₁ := comp0_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n
  have h₂ := comp1_genericPoint_specializes 𝔛 κ (toκ.comp ρO) n
  have hy₂ := comp1_snd_eq_comp0_fst 𝔛 κ (toκ.comp ρO) n
  obtain ⟨hy₁', hy₂'⟩ := comp0_genericPoint_ne_and_comp1_genericPoint_ne 𝔛 κ O ρO toκ n

  have htri := frame_eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal 𝔛 κ (toκ.comp ρO) n
  obtain ⟨hPm, hQm, hPQ', hQP'⟩ := frame_branchIdeal_ne_maximalIdeal_and_not_le 𝔛 κ O ρO hϖ toκ n hy₁' hy₂'

  have hJ₁le : RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 0).stalkMap
      ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom ≤ Scheme.branchIdeal h₁ :=
    TransvChair.ker_stalkMap_le_comap_stalkSpecializes (𝔛.comp κ (toκ.comp ρO) 0) (genericPoint_specializes _)
  have hJ₂le : (RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 1).stalkMap
      ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom).comap
      ((DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom ≤
      Scheme.branchIdeal h₂ := by
    refine (Ideal.comap_mono (TransvChair.ker_stalkMap_le_comap_stalkSpecializes (𝔛.comp κ (toκ.comp ρO) 1)
      (genericPoint_specializes ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)))).trans
      (le_of_eq ?_)
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, TopCat.Presheaf.stalkSpecializes_comp]
    rfl

  haveI hJ₁p : (RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 0).stalkMap
      ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p : (RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 1).stalkMap
      ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p' : ((RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 1).stalkMap
      ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom).comap
      ((DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom).IsPrime :=
    Ideal.comap_isPrime _ _
  have hJ₁ : RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 0).stalkMap
      ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom = Scheme.branchIdeal h₁ :=
    eq_branchIdeal_of_isPrime_of_le h₁ h₂ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQP' _ hJ₁le
  have hJ₂ : (RingHom.ker ((𝔛.comp κ (toκ.comp ρO) 1).stalkMap
      ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)).hom).comap
      ((DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom =
      Scheme.branchIdeal h₂ :=
    eq_branchIdeal_of_isPrime_of_le h₂ h₁ (fun 𝔮 h𝔮 => (htri 𝔮).imp id Or.symm) hQm hPQ' _ hJ₂le

  have hrad : (Scheme.branchIdeal h₁ ⊔ Scheme.branchIdeal h₂).IsRadical := by
    have h := TransvChair.isRadical_comap_ker_sup_comap_ker (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) n _ rfl hy₂
    have e : (DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq
        (rfl : (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) =
          (𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n))) = 𝟙 _ :=
      (DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)).presheaf.stalkSpecializes_refl _
    rw [e, CommRingCat.hom_id, Ideal.comap_id, hJ₁, hJ₂] at h
    exact h
  have hκ : Scheme.branchIdeal h₁ ⊔ Scheme.branchIdeal h₂ = IsLocalRing.maximalIdeal _ :=
    eq_of_isRadical_of_le_of_forall_le hrad
      (sup_le (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)))
      (fun 𝔮 h𝔮 hle => by
        rcases htri 𝔮 with rfl | rfl | rfl
        · exact le_rfl
        · exact absurd (le_sup_right.trans hle) hQP'
        · exact absurd (le_sup_left.trans hle) hPQ')

  have E : (DRLevel.bcMap (N₀ := N₀) ρO toκ).base
        ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)) =
      (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)).base
        ((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)).base
          ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n))) := by
    rw [← Scheme.Hom.comp_apply (fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ))
        (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)),
      ECL_TransvPlumb.g_comp_j ρO hϖ toκ]
  have hι := (ConcreteCategory.bijective_of_isIso
    ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkCongr (.of_eq E)).hom).2
  have hπ := ECL_TransvPlumb.stalkMap_j_surjective ρO
    ((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)).base
      ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)))
  have hθ : Function.Surjective
      (((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkCongr (.of_eq E)).hom ≫
        (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)).stalkMap
          ((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)).base
            ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)))).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact hπ.comp hι
  have hψ := ECL_TransvPlumb.flat_stalkMap_g ρO hϖ toκ
    ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n))
  have hfac : ((DRLevel.bcMap (N₀ := N₀) ρO toκ).stalkMap
        ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n))).hom =
      ((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)).stalkMap
          ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n))).hom.comp
        (((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkCongr (.of_eq E)).hom ≫
          (DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O)).stalkMap
            ((fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ)).base
              ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)))).hom := by
    rw [ECL_TransvPlumb.stalkMap_bcMap_eq ρO hϖ toκ, CommRingCat.hom_comp,
      CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc]

  have hP := TransvChair.comap_stalkMap_comap_stalkSpecializes (DRLevel.bcMap (N₀ := N₀) ρO toκ) h₁
  have hQ := TransvChair.comap_stalkMap_comap_stalkSpecializes (DRLevel.bcMap (N₀ := N₀) ρO toκ) h₂
  rw [hfac] at hP hQ
  change (Scheme.branchIdeal h₁).comap _ =
    Scheme.branchIdeal ((DRLevel.bcMap (N₀ := N₀) ρO toκ).base.hom.map_specializes h₁) at hP
  change (Scheme.branchIdeal h₂).comap _ =
    Scheme.branchIdeal ((DRLevel.bcMap (N₀ := N₀) ρO toκ).base.hom.map_specializes h₂) at hQ

  have hPQ : Scheme.branchIdeal ((DRLevel.bcMap (N₀ := N₀) ρO toκ).base.hom.map_specializes h₁) ≠
      Scheme.branchIdeal ((DRLevel.bcMap (N₀ := N₀) ρO toκ).base.hom.map_specializes h₂) :=
    fun h => ModularCurve.DRModelPackageLevel.xiInf_ne_xiZero N₀ q hqN 𝔛 O ρO hϖ κ toκ
      (by
        show (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base _ = (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base _
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact eq_of_branchIdeal_eq _ _ h)

  have H := TransvChair.descent _ hθ _ hψ hP hQ hPQ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQm hPQ' hQP' hκ

  have ey : (DRLevel.bcMap (N₀ := N₀) ρO toκ).base
      ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)) =
      𝔛.crossingPt ρO toκ n := by
    show _ = (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫
      DRLevel.bcMap ρO toκ).base n
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have eξ₁ : (DRLevel.bcMap (N₀ := N₀) ρO toκ).base
      ((𝔛.comp κ (toκ.comp ρO) 0).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) = 𝔛.ξinf ρO toκ := by
    show _ = (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have eξ₂ : (DRLevel.bcMap (N₀ := N₀) ρO toκ).base
      ((𝔛.comp κ (toκ.comp ρO) 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) = 𝔛.ξzero ρO toκ := by
    show _ = (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  exact TransvChair.branchIdeal_sup_eq_transport ey eξ₁ eξ₂ _ _ hinf hzero H

end Main

end S_ModularCurve_DRModelPackageLevel_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal (solution)
