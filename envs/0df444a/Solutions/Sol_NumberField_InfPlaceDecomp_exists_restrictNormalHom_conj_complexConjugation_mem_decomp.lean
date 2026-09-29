-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.exists_restrictNormalHom_conj_complexConjugation_mem_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c688c795-d807-5f95-aef9-526b21e83fa4

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp

set_option autoImplicit false
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp.NumberField IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField.PlaceDecomp NumberField.InfPlaceDecomp P2MW.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp.NumberField.InfPlaceDecomp"

namespace NumberField
p2m_export "NumberField" "InfinitePlace.mk_embedding IsTotallyComplex IsTotallyComplex.complexEmbedding_not_isReal mk place ComplexEmbedding.IsConj InfinitePlace.mem_stabilizer_mk_iff InfinitePlace.mk InfinitePlace ComplexEmbedding.isConj_one_iff ComplexEmbedding.conjugate_coe_eq InfPlaceDecomp.decomp"
namespace InfPlaceDecomp
p2m_export "NumberField.InfPlaceDecomp" "decomp"
namespace ArchBridge
p2m_open "NumberField.InfPlaceDecomp NumberField"

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

lemma exists_aut_comp_eq (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] (ψ₁ ψ₂ : ↥F →ₐ[ℚ] ℂ) :
    ∃ g : ↥F ≃ₐ[ℚ] ↥F, ∀ x : ↥F, ψ₁ (g x) = ψ₂ x := by
  letI : Algebra ↥F ℂ := ψ₁.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥F ℂ := IsScalarTower.of_algebraMap_eq fun r => (ψ₁.commutes r).symm
  exact ⟨ψ₂.restrictNormal' ↥F, fun x => AlgHom.restrictNormal_commutes ψ₂ ↥F x⟩

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥F]

lemma coe_restrictNormalHom_apply (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥F) :
    ((AlgEquiv.restrictNormalHom ↥F τ x : ↥F) : AlgebraicClosure ℚ) = τ (x : AlgebraicClosure ℚ) :=
  AlgEquiv.restrictNormal_commutes τ ↥F x

lemma exists_gal_comp_eq (φ : ↥F →+* ℂ) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x : ↥F, complexEmbedding (σ (x : AlgebraicClosure ℚ)) = φ x := by
  obtain ⟨g, hg⟩ := exists_aut_comp_eq F (complexEmbedding.comp F.val) φ.toRatAlgHom
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥F) (AlgebraicClosure ℚ) g
  refine ⟨σ, fun x => ?_⟩
  rw [← coe_restrictNormalHom_apply F σ x, hσ]
  exact hg x

lemma isConj_restrictNormalHom (φ : ↥F →+* ℂ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : ↥F, complexEmbedding (σ (x : AlgebraicClosure ℚ)) = φ x) :
    ComplexEmbedding.IsConj φ (AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ)) := by
  refine RingHom.ext fun x => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hσ x]
  change _ = φ ((AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ)) x)
  rw [← hσ, coe_restrictNormalHom_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    ← AlgEquiv.mul_apply σ σ⁻¹, mul_inv_cancel, AlgEquiv.one_apply, complexEmbedding_complexConjugation]

end NumberField.InfPlaceDecomp.ArchBridge

open NumberField.InfPlaceDecomp.ArchBridge CategoryTheory _root_.NumberField _root_.P2MW.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp.NumberField IsDedekindDomain ExtCitation in

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
    (w : InfinitePlace ↥F) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ) ∈ NumberField.InfPlaceDecomp.decomp ℚ ↥F w ∧
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ) ≠ 1 ∧
      (∀ d : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w),
        (d : ↥F ≃ₐ[ℚ] ↥F) = 1 ∨ (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ)) ∧
      σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup := by

  obtain ⟨σ, hσ⟩ := exists_gal_comp_eq F w.embedding
  have hconj := isConj_restrictNormalHom F w.embedding σ hσ
  have hne : AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ) ≠ 1 := by
    intro h1
    rw [h1, ComplexEmbedding.isConj_one_iff] at hconj
    exact IsTotallyComplex.complexEmbedding_not_isReal _ hconj
  refine ⟨σ, ?_, hne, ?_, ?_⟩
  ·
    change _ ∈ MulAction.stabilizer (↥F ≃ₐ[ℚ] ↥F) w
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mem_stabilizer_mk_iff]
    exact Or.inr hconj
  ·
    intro d
    have hd : (d : ↥F ≃ₐ[ℚ] ↥F) ∈ MulAction.stabilizer (↥F ≃ₐ[ℚ] ↥F) (InfinitePlace.mk w.embedding) := by
      rw [InfinitePlace.mk_embedding]; exact d.2
    rw [InfinitePlace.mem_stabilizer_mk_iff] at hd
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr (h.ext hconj)
  ·
    intro hfix
    apply hne
    rw [IntermediateField.mem_fixingSubgroup_iff] at hfix
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [coe_restrictNormalHom_apply, AlgEquiv.one_apply]
    exact hfix _ x.2

end S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp (solution)
