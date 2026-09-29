-- Prove2me | solution 1 for ModularCurve.DRModelPackage.baseChangeMap_genericPoint_mem_preimage_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/34145eef-a044-5ab8-8627-23cdc065a024

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ssJSet_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage ssJSet DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero ssJSet_nonempty ssJSet_finite"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "smoothLocus crossing_card compInf_isClosedImmersion compZero_isClosedImmersion compZero ratModel compInf mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero"
namespace GenericPoints
p2m_open "ModularCurve.DRModelPackage ModularCurve"

theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
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

theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
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

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

theorem not_surjective_of_crossing (f : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) → ↥(𝔛.ratModel κ).C) :
    ¬ Function.Surjective f := by
  classical
  intro hf

  haveI : Infinite ↥(𝔛.ratModel κ).C := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton (𝔛.ratModel κ).toBase
    exact Set.infinite_univ_iff.mp (Set.infinite_univ_iff.mpr
      (Set.infinite_univ_iff.mp ((h.mono (Set.subset_univ _)))))
  haveI : Infinite ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) := Infinite.of_surjective f hf
  have h0 : Nat.card ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) = 0 := Nat.card_eq_zero_of_infinite
  rw [𝔛.crossing_card κ] at h0
  haveI : Finite ↥(ssJSet p κ) := (ssJSet_finite p κ).to_subtype
  haveI : Nonempty ↥(ssJSet p κ) := (ssJSet_nonempty (q := p) (k := κ)).to_subtype
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ h0

theorem compInf_genericPoint_notMem_range_compZero :
    (𝔛.compInf κ).base (genericPoint ↥(𝔛.ratModel κ).C) ∉ Set.range ⇑(𝔛.compZero κ).base := fun h =>
  haveI := 𝔛.compZero_isClosedImmersion κ
  not_surjective_of_crossing p 𝔛 κ _ (surjective_fst_of_mem_range _ _ h)

theorem compZero_genericPoint_notMem_range_compInf :
    (𝔛.compZero κ).base (genericPoint ↥(𝔛.ratModel κ).C) ∉ Set.range ⇑(𝔛.compInf κ).base := fun h =>
  haveI := 𝔛.compInf_isClosedImmersion κ
  not_surjective_of_crossing p 𝔛 κ _ (surjective_snd_of_mem_range _ _ h)

end ModularCurve.DRModelPackage.GenericPoints

open ModularCurve.DRModelPackage.GenericPoints in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ∈
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus ∧
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ∈
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus := by
  have hfst : DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = pullback.fst (DRModel.toBase p) _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]

  have key : ∀ (i : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
      (c : (𝔛.ratModel κ).C),
      (i ≫ DRModel.baseChangeMap toκ).base c ∈
          (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus ↔
        i.base c ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ 𝔛.smoothLocus := by
    intro i c
    change ((i ≫ DRModel.baseChangeMap toκ) ≫ pullback.fst (DRModel.toBase p) _).base c ∈ 𝔛.smoothLocus ↔
      (i ≫ pullback.fst (DRModel.toBase p) _).base c ∈ 𝔛.smoothLocus
    rw [Category.assoc, hfst]
  refine ⟨(key _ _).mpr ?_, (key _ _).mpr ?_⟩
  · rw [ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero]
    exact fun h => compInf_genericPoint_notMem_range_compZero p 𝔛 κ h.2
  · rw [ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero]
    exact fun h => compZero_genericPoint_notMem_range_compInf p 𝔛 κ h.1

end S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus (solution)
