-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1a79c3f9-f013-5a88-9f57-0a20929c9389

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField

theorem solution
    (E C : Type) [Field E] [NumberField E] [Field C] [NumberField C] [Algebra E C] [IsGalois E C]
    (M : Subgroup (C ≃ₐ[E] C))
    (hM : ∀ (φ : C →+* ℂ) (σ : C ≃ₐ[E] C), NumberField.ComplexEmbedding.IsConj φ σ → σ ∈ M)
    [IsGalois E (IntermediateField.fixedField M)] :
    ∀ (w : InfinitePlace (IntermediateField.fixedField M)) (g : (IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)),
      g ∈ NumberField.InfPlaceDecomp.decomp E (IntermediateField.fixedField M) w → g = 1 := by
  intro w g hg

  suffices hunr : w.IsUnramified E by
    have hbot := (NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot.1 hunr)
    have : g ∈ (⊥ : Subgroup ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M))) := by
      rw [← hbot]; exact hg
    exact Subgroup.mem_bot.1 this

  obtain ⟨W, hW⟩ := NumberField.InfinitePlace.comap_surjective (k := ↥(IntermediateField.fixedField M)) (K := C) w
  change W.comap (algebraMap (↥(IntermediateField.fixedField M)) C) = w at hW
  rw [NumberField.InfinitePlace.isUnramified_iff]
  by_cases hE : (W.comap (algebraMap E C)).IsComplex
  ·
    right
    rw [← hW, ← NumberField.InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
    exact hE
  left
  by_cases hWr : W.IsReal
  · rw [← hW]
    exact hWr.comap _

  have hram : W.IsRamified E := by
    rw [NumberField.InfinitePlace.isRamified_iff]
    exact ⟨NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hWr, NumberField.InfinitePlace.not_isComplex_iff_isReal.1 hE⟩
  have hcard := NumberField.InfinitePlace.isRamified_iff_card_stabilizer_eq_two.1 hram
  have hne : MulAction.stabilizer (C ≃ₐ[E] C) W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard (by decide)
  obtain ⟨⟨c, hc⟩, hc1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
  rw [← NumberField.InfinitePlace.mk_embedding W] at hc
  have hconj : NumberField.ComplexEmbedding.IsConj W.embedding c :=
    ((NumberField.InfinitePlace.mem_stabilizer_mk_iff W.embedding c).1 hc).resolve_left hc1

  have hfix : ∀ x : ↥(IntermediateField.fixedField M), c (x : C) = x := fun x =>
    (IntermediateField.mem_fixedField_iff M (x : C)).1 x.2 c (hM _ c hconj)

  have hψ : NumberField.ComplexEmbedding.IsReal (W.embedding.comp (algebraMap (↥(IntermediateField.fixedField M)) C)) := by
    rw [NumberField.ComplexEmbedding.IsReal, IsSelfAdjoint]
    apply RingHom.ext
    intro x
    change star (W.embedding (algebraMap _ C x)) = W.embedding (algebraMap _ C x)
    rw [← hconj.eq]
    exact congrArg W.embedding (hfix x)
  rw [← hW, ← NumberField.InfinitePlace.mk_embedding W, NumberField.InfinitePlace.comap_mk, NumberField.InfinitePlace.isReal_mk_iff]
  exact hψ

end S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem (solution)
