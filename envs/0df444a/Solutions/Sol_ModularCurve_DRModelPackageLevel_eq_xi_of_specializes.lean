-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.eq_xi_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b611fb59-33e7-5efc-80c0-346e2de64899

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_eq_xi_of_specializes
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

noncomputable section

namespace ECL_EqGen

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

section Main
variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  {O : Type} [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)

include hϖ in

private theorem eq_of_specializes_aux [IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (i : DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO) ⟶ DRLevel.fibre (N₀ := N₀) (toκ.comp ρO))
    (hi : ∀ z, z ⤳ i.base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) →
      z = i.base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))
    (y : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hy : y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (h : y ⤳ (i ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) :
    y = (i ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) := by
  set η := genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))
  set g := fibreMapOfComp (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) (toκ.comp ρO) (ι hϖ toκ) (ι_comp ρO hϖ toκ) with hg
  set j := DRLevel.bcMap (N₀ := N₀) ρO (IsLocalRing.residue O) with hj
  haveI : IsClosedImmersion j := by
    rw [hj, bcMap_eq_fibreMapOfComp]
    exact isClosedImmersion_fibreMapOfComp _ _ _ rfl Ideal.Quotient.mk_surjective
  haveI : Flat g := flat_fibreMapOfComp _ _ _ _
  have hξ : (i ≫ DRLevel.bcMap ρO toκ).base η = j.base (g.base (i.base η)) := by
    rw [bcMap_eq_comp ρO hϖ toκ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [hξ] at h ⊢
  obtain ⟨y₀, rfl⟩ := exists_bcMap_residue_eq ρO hϖ y hy
  have h₀ : y₀ ⤳ g.base (i.base η) := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  rw [← hgz, hi z hz]

end Main

end ECL_EqGen

end

open ECL_EqGen in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) :
    (∀ y : ↥(DRLevel.XO (N₀ := N₀) ρO), y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y ⤳ 𝔛.ξinf ρO toκ → y = 𝔛.ξinf ρO toκ) ∧
    (∀ y : ↥(DRLevel.XO (N₀ := N₀) ρO), y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y ⤳ 𝔛.ξzero ρO toκ → y = 𝔛.ξzero ρO toκ) := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  exact ⟨fun y hy h => ECL_EqGen.eq_of_specializes_aux ρO hϖ toκ (𝔛.comp κ (toκ.comp ρO) 0)
      (ECL_EqGen.eq_of_specializes_comp0_genericPoint 𝔛 κ (toκ.comp ρO)) y hy h,
    fun y hy h => ECL_EqGen.eq_of_specializes_aux ρO hϖ toκ (𝔛.comp κ (toκ.comp ρO) 1)
      (ECL_EqGen.eq_of_specializes_comp1_genericPoint 𝔛 κ (toκ.comp ρO)) y hy h⟩

end S_ModularCurve_DRModelPackageLevel_eq_xi_of_specializes
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_eq_xi_of_specializes (solution)
