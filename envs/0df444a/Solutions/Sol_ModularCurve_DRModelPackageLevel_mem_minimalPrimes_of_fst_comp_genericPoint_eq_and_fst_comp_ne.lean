-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/486a05fa-3667-54da-9ede-a58d9c35267b

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

noncomputable section

private theorem g2L_comp_base_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).base x = g.base (f.base x) := by
  rw [Scheme.Hom.comp_base]; rfl

private theorem g2L_range_comp_eq {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  ext z
  simp only [Set.mem_range, Set.mem_image, g2L_comp_base_apply]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨f.base x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩

private theorem g2L_range_subset_of_mem {C Z : Scheme} [IrreducibleSpace C] (i : C ⟶ Z) (S : Set Z) (hS : IsClosed S)
    (h : i.base (genericPoint C) ∈ S) : Set.range i.base ⊆ S := by
  have h1 : Set.range ⇑i.base = ⇑i.base '' closure {genericPoint C} := by
    rw [genericPoint_closure, Set.image_univ]
  rw [h1]
  refine (image_closure_subset_closure_image i.base.hom.continuous).trans ?_
  rw [Set.image_singleton]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hS

private theorem g2L_isDVR (q : ℕ) [Fact q.Prime] : IsDiscreteValuationRing (DRLevel.R q) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out

attribute [local instance] g2L_isDVR

private theorem g2L_hϖ (q : ℕ) [Fact q.Prime] :
    IsLocalRing.maximalIdeal (DRLevel.R q) = Ideal.span {((q : ℕ) : DRLevel.R q)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (GaloisRep.irreducible_natCast_ratLocalizedAt q Fact.out)

section Engine
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

private theorem g2L_wκ_invol :
    DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ ≫ DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [DRLevel.fibreMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [𝔓.w_invol, Category.comp_id]
  · simp only [DRLevel.fibreMap, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

private theorem g2L_comp_one_wκ : 𝔓.comp κ toκ 1 ≫ DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ = 𝔓.comp κ toκ 0 := by
  rw [← 𝔓.comp_w κ toκ, Category.assoc, g2L_wκ_invol, Category.comp_id]

private theorem g2L_range_zero_not_subset :
    ¬ (Set.range (𝔓.comp κ toκ 0).base ⊆ Set.range (𝔓.comp κ toκ 1).base) := by
  intro h
  apply 𝔓.range_comp_ne κ toκ
  refine h.antisymm ?_
  have h1 := Set.image_mono (f := ⇑(DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base) h
  rwa [← g2L_range_comp_eq, ← g2L_range_comp_eq, 𝔓.comp_w, g2L_comp_one_wκ] at h1

private theorem g2L_range_one_not_subset :
    ¬ (Set.range (𝔓.comp κ toκ 1).base ⊆ Set.range (𝔓.comp κ toκ 0).base) := by
  intro h
  apply 𝔓.range_comp_ne κ toκ
  refine Set.Subset.antisymm ?_ h
  have h1 := Set.image_mono (f := ⇑(DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base) h
  rwa [← g2L_range_comp_eq, ← g2L_range_comp_eq, 𝔓.comp_w, g2L_comp_one_wκ] at h1

variable [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]

private theorem g2L_c0_notMem :
    (𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range (𝔓.comp κ toκ 1).base := by
  intro h
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  exact g2L_range_zero_not_subset N₀ q hqN 𝔓 κ toκ
    (g2L_range_subset_of_mem _ _ (𝔓.comp κ toκ 1).isClosedEmbedding.isClosed_range h)

private theorem g2L_c1_notMem :
    (𝔓.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range (𝔓.comp κ toκ 0).base := by
  intro h
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  exact g2L_range_one_not_subset N₀ q hqN 𝔓 κ toκ
    (g2L_range_subset_of_mem _ _ (𝔓.comp κ toκ 0).isClosedEmbedding.isClosed_range h)

private theorem g2L_eq_of_specializes_c0 (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  rcases 𝔓.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔓.comp κ toκ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔓.comp κ toκ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (g2L_c0_notMem N₀ q hqN 𝔓 κ toκ)

private theorem g2L_eq_of_specializes_c1 (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔓.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔓.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  rcases 𝔓.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔓.comp κ toκ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (g2L_c1_notMem N₀ q hqN 𝔓 κ toκ)
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔓.comp κ toκ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

section Local
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
  (κ : Type) [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)

private theorem g2L_toκ_maximalIdeal (a : DRLevel.R q) (ha : a ∈ IsLocalRing.maximalIdeal (DRLevel.R q)) : toκ a = 0 := by
  rw [g2L_hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

private def g2L_ι : IsLocalRing.ResidueField (DRLevel.R q) →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (DRLevel.R q)) toκ (g2L_toκ_maximalIdeal q κ toκ)

private theorem g2L_ι_comp_residue : (g2L_ι q κ toκ).comp (IsLocalRing.residue (DRLevel.R q)) = toκ :=
  RingHom.ext fun _ => rfl

private def g2L_bc {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) : DRLevel.fibre (N₀ := N₀) ρB ⟶ DRLevel.fibre (N₀ := N₀) ρA :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ])

private theorem g2L_bc_fst {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) :
    g2L_bc N₀ q ρA ρB φ hφ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [g2L_bc, pullback.lift_fst, Category.comp_id]

private theorem g2L_bc_snd {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) :
    g2L_bc N₀ q ρA ρB φ hφ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [g2L_bc, pullback.lift_snd]

private theorem g2L_isPullback_bc {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) :
    IsPullback (g2L_bc N₀ q ρA ρB φ hφ)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρB)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρA)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ρA) = Spec.map (CommRingCat.ofHom ρB) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  refine IsPullback.of_right ?_ (g2L_bc_snd N₀ q ρA ρB φ hφ)
    (IsPullback.of_hasPullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρA)))
  have h1 := g2L_bc_fst N₀ q ρA ρB φ hφ
  convert IsPullback.of_hasPullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρB)) using 1

private theorem g2L_exists_fst_residue_eq (y : ↥(DRLevel.X N₀ q))
    (hy : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base y).asIdeal) :
    ∃ y₀ : ↥(DRLevel.fibre (N₀ := N₀) (IsLocalRing.residue (DRLevel.R q))),
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q))))).base y₀ = y := by
  set s := (DRLevel.toBase N₀ q).base y with hs
  have hsm : s = IsLocalRing.closedPoint (DRLevel.R q) := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal (DRLevel.R q) ≤ s.asIdeal := by
      rw [g2L_hϖ, Ideal.span_singleton_le_iff_mem]
      exact hy
    exact ((IsLocalRing.maximalIdeal.isMaximal (DRLevel.R q)).eq_of_le s.isPrime.ne_top hle).symm
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (DRLevel.R q))) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (DRLevel.R q))
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := DRLevel.toBase N₀ q)
    (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) y
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField (DRLevel.R q))) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

private theorem g2L_isClosedImmersion_fst_residue :
    IsClosedImmersion (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q))))) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  exact MorphismProperty.pullback_fst _ _ inferInstance

private theorem g2L_flat_bc_ι :
    Flat (g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ)) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (g2L_ι q κ toκ))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (g2L_ι q κ toκ).toAlgebra
    show RingHom.Flat (algebraMap (IsLocalRing.ResidueField (DRLevel.R q)) κ)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat (IsLocalRing.ResidueField (DRLevel.R q)) κ)
  exact MorphismProperty.of_isPullback (g2L_isPullback_bc N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).flip inferInstance

private theorem g2L_surjective_bc_ι :
    Surjective (g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom (g2L_ι q κ toκ))) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint κ,
      (inferInstance : Subsingleton (PrimeSpectrum (IsLocalRing.ResidueField (DRLevel.R q)))).elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (g2L_isPullback_bc N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).flip inferInstance

end Local

section Main
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
  [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]

private theorem g2L_mem_toBase_fst (z : ↥(DRLevel.fibre (N₀ := N₀) toκ)) :
    ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z)).asIdeal := by
  have hsq : (DRLevel.toBase N₀ q).base ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z) =
      (Spec.map (CommRingCat.ofHom toκ)).base ((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z) :=
    congr($(pullback.condition (f := DRLevel.toBase N₀ q) (g := Spec.map (CommRingCat.ofHom toκ))).base z)
  rw [hsq]
  change ((q : ℕ) : DRLevel.R q) ∈ (PrimeSpectrum.comap toκ
    ((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z)).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]
  exact Ideal.zero_mem _

private theorem g2L_fstmax (cmp : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hmax : ∀ z : ↥(DRLevel.fibre (N₀ := N₀) toκ), z ⤳ cmp.base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) → z = cmp.base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)))
    (y : ↥(DRLevel.X N₀ q)) (hy : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base y).asIdeal)
    (h : y ⤳ (cmp ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    y = (cmp ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  set η := genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)
  set g := g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ) with hg
  set j := pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) with hj
  haveI : IsClosedImmersion j := g2L_isClosedImmersion_fst_residue N₀ q
  haveI : Flat g := g2L_flat_bc_ι N₀ q κ toκ
  have hfac : pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) = g ≫ j := (g2L_bc_fst N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).symm
  have hξ : (cmp ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η = j.base (g.base (cmp.base η)) := by
    rw [hfac, g2L_comp_base_apply, g2L_comp_base_apply]
  rw [hξ] at h ⊢
  obtain ⟨y₀, rfl⟩ := g2L_exists_fst_residue_eq N₀ q y hy
  have h₀ : y₀ ⤳ g.base (cmp.base η) := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  rw [← hgz, hmax z hz]

private theorem g2L_chart_key {A : Type} [CommRing A] [Algebra (DRLevel.R q) A]
    (ιC : Spec (CommRingCat.of A) ⟶ DRLevel.X N₀ q) [IsOpenImmersion ιC]
    (hιC : ιC ≫ DRLevel.toBase N₀ q = Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) A)))
    (ξ : ↥(DRLevel.X N₀ q)) (hξq : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base ξ).asIdeal)
    (hm : ∀ y : ↥(DRLevel.X N₀ q), ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base y).asIdeal → y ⤳ ξ → y = ξ)
    (P : PrimeSpectrum A) (hP : ξ = ιC.base P) :
    P.asIdeal ∈ (Ideal.span {((q : ℕ) : A)}).minimalPrimes := by

  have hfib : ∀ Q : PrimeSpectrum A, ((q : ℕ) : A) ∈ Q.asIdeal ↔
      ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base (ιC.base Q)).asIdeal := by
    intro Q
    have hsq : (DRLevel.toBase N₀ q).base (ιC.base Q) = (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) A))).base Q := by
      rw [← g2L_comp_base_apply, hιC]
    rw [hsq]
    change _ ↔ ((q : ℕ) : DRLevel.R q) ∈ (PrimeSpectrum.comap (algebraMap (DRLevel.R q) A) Q).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast]
  have hqP : ((q : ℕ) : A) ∈ P.asIdeal := by rw [hfib, ← hP]; exact hξq
  refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hqP⟩, ?_⟩
  rintro Q ⟨hQ, hqQ⟩ hQP

  let Q' : PrimeSpectrum A := ⟨Q, hQ⟩
  have hsp : ιC.base Q' ⤳ ξ := by
    rw [hP]
    exact ((PrimeSpectrum.le_iff_specializes Q' P).mp hQP).map ιC.base.hom.continuous
  have hQq : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base (ιC.base Q')).asIdeal :=
    (hfib Q').mp ((Ideal.span_singleton_le_iff_mem _).mp hqQ)
  have heq : ιC.base Q' = ιC.base P := by rw [← hP]; exact hm _ hQq hsp
  have hQP' : Q' = P := ιC.isOpenEmbedding.injective heq
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal hQP').symm

include hqN 𝔓 in

private theorem g2L_exists_index_eq (𝔮 : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (h𝔮 : 𝔮 ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes) :
    ∃ (i : Fin 2) (h : 𝔮.IsPrime),
      (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) = (IgusaScheme.ιFin (N₀ * q) q).base ⟨𝔮, h⟩ := by
  set A := ↥(IgusaScheme.chartAlgFin (N₀ * q) q) with hA
  set ιF := IgusaScheme.ιFin (N₀ * q) q with hιF
  have hprime : 𝔮.IsPrime := h𝔮.1.1
  have hq𝔮 : ((q : ℕ) : A) ∈ 𝔮 := (Ideal.span_singleton_le_iff_mem _).mp h𝔮.1.2
  let Q : PrimeSpectrum A := ⟨𝔮, hprime⟩

  have hfib : ∀ Q : PrimeSpectrum A, ((q : ℕ) : A) ∈ Q.asIdeal ↔
      ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base (ιF.base Q)).asIdeal := by
    intro Q
    have hsq : (DRLevel.toBase N₀ q).base (ιF.base Q) =
        (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) A))).base Q := by
      rw [← g2L_comp_base_apply, hιF, IgusaScheme.ιFin_igusaTo]
    rw [hsq]
    change _ ↔ ((q : ℕ) : DRLevel.R q) ∈ (PrimeSpectrum.comap (algebraMap (DRLevel.R q) A) Q).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast]
  have hxq : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base (ιF.base Q)).asIdeal := (hfib Q).mp hq𝔮

  set g := g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ) with hg
  set j := pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) with hj
  have hfac : pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) = g ≫ j := (g2L_bc_fst N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).symm
  obtain ⟨y₀, hy₀⟩ := g2L_exists_fst_residue_eq N₀ q (ιF.base Q) hxq
  haveI : Surjective g := g2L_surjective_bc_ι N₀ q κ toκ
  obtain ⟨z, hz⟩ := (inferInstance : Surjective g).surj y₀
  have hzx : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z = ιF.base Q := by
    rw [hfac, g2L_comp_base_apply, hz, hy₀]

  obtain ⟨i, c, hc⟩ : ∃ (i : Fin 2) (c : ↥(DRLevel.fibre0 (N₀ := N₀) toκ)), (𝔓.comp κ toκ i).base c = z := by
    rcases 𝔓.comp_jointly_surjective κ toκ z with ⟨c, hc⟩ | ⟨c, hc⟩
    exacts [⟨0, c, hc⟩, ⟨1, c, hc⟩]
  refine ⟨i, hprime, ?_⟩

  have hsp : (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ⤳ ιF.base Q := by
    rw [← hzx, ← hc, g2L_comp_base_apply]
    exact ((genericPoint_specializes c).map (𝔓.comp κ toκ i).base.hom.continuous).map
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base.hom.continuous

  have hmem : (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∈ Set.range ιF.base :=
    hsp.mem_open ιF.isOpenEmbedding.isOpen_range ⟨Q, rfl⟩
  obtain ⟨Q', hQ'⟩ := hmem
  have hQ'Q : Q' ⤳ Q := by
    rw [← hQ'] at hsp
    exact ιF.isOpenEmbedding.isInducing.specializes_iff.mp hsp
  have hle : Q'.asIdeal ≤ 𝔮 := (PrimeSpectrum.le_iff_specializes Q' Q).mpr hQ'Q
  have hqQ' : ((q : ℕ) : A) ∈ Q'.asIdeal := by
    rw [hfib, hQ', g2L_comp_base_apply]
    exact g2L_mem_toBase_fst N₀ q κ toκ _
  have hge : 𝔮 ≤ Q'.asIdeal := h𝔮.2 ⟨Q'.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hqQ'⟩ hle
  have hQQ : Q' = Q := PrimeSpectrum.ext (le_antisymm hle hge)
  rw [← hQ', hQQ]

end Main

end

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (∀ (i : Fin 2) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      𝔮.asIdeal ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes) ∧
    (∀ (i : Fin 2) (𝔯 : PrimeSpectrum ↥(IgusaScheme.chartAlgInf (N₀ * q) q)),
      (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιInf (N₀ * q) q).base 𝔯 →
      𝔯.asIdeal ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N₀ * q) q))}).minimalPrimes) ∧
    (𝔓.comp κ toκ 0 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ≠
      (𝔓.comp κ toκ 1 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  set η := genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) with hη

  have hmax0 := g2L_fstmax N₀ q κ toκ (𝔓.comp κ toκ 0) (g2L_eq_of_specializes_c0 N₀ q hqN 𝔓 κ toκ)
  have hmax1 := g2L_fstmax N₀ q κ toκ (𝔓.comp κ toκ 1) (g2L_eq_of_specializes_c1 N₀ q hqN 𝔓 κ toκ)
  have hmax : ∀ i : Fin 2, ∀ y : ↥(DRLevel.X N₀ q), ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base y).asIdeal →
      y ⤳ (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η → y = (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η :=
    Fin.forall_fin_two.mpr ⟨hmax0, hmax1⟩

  have hpq : ∀ i : Fin 2, ((q : ℕ) : DRLevel.R q) ∈
      ((DRLevel.toBase N₀ q).base ((𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η)).asIdeal := by
    intro i
    rw [g2L_comp_base_apply]
    exact g2L_mem_toBase_fst N₀ q κ toκ _
  refine ⟨?_, ?_, ?_⟩
  · intro i 𝔮 h𝔮
    exact g2L_chart_key N₀ q (IgusaScheme.ιFin (N₀ * q) q) (IgusaScheme.ιFin_igusaTo (N₀ * q) q) _ (hpq i) (hmax i) 𝔮 h𝔮
  · intro i 𝔯 h𝔯
    exact g2L_chart_key N₀ q (IgusaScheme.ιInf (N₀ * q) q) (IgusaScheme.ιInf_igusaTo (N₀ * q) q) _ (hpq i) (hmax i) 𝔯 h𝔯
  ·
    intro heq
    have hall : ∀ i i' : Fin 2, (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η = (𝔓.comp κ toκ i' ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η :=
      Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨rfl, heq⟩, Fin.forall_fin_two.mpr ⟨heq.symm, rfl⟩⟩
    obtain ⟨-, hcard, -, -⟩ :=
      ModularCurve.IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd N₀ q hqN
    obtain ⟨𝔮₁, 𝔮₂, hne, hpair⟩ := Set.ncard_eq_two.mp hcard
    have h₁ : 𝔮₁ ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes := by
      rw [hpair]; exact Set.mem_insert _ _
    have h₂ : 𝔮₂ ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes := by
      rw [hpair]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    obtain ⟨i₁, hp₁, he₁⟩ := g2L_exists_index_eq N₀ q hqN 𝔓 κ toκ 𝔮₁ h₁
    obtain ⟨i₂, hp₂, he₂⟩ := g2L_exists_index_eq N₀ q hqN 𝔓 κ toκ 𝔮₂ h₂
    have hιeq : (IgusaScheme.ιFin (N₀ * q) q).base ⟨𝔮₁, hp₁⟩ = (IgusaScheme.ιFin (N₀ * q) q).base ⟨𝔮₂, hp₂⟩ := by
      rw [← he₁, ← he₂]; exact hall i₁ i₂
    exact hne (congrArg PrimeSpectrum.asIdeal ((IgusaScheme.ιFin (N₀ * q) q).isOpenEmbedding.injective hιeq))

end S_ModularCurve_DRModelPackageLevel_mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne (solution)
