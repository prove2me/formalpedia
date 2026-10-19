-- Prove2me | solution 1 for MazurTransfer.DivisorSectionSpaceFieldAction.image_lSpaceOn
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:55:19.561383+00:00
-- url     : https://prove2.me/submissions/f883b559-b26b-4ed0-9cf0-0a89eddfcee2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: section spaces with valuation bounds transport under field
and place automorphisms. Named downstream consumer: the transformed range
condition in divisor presentations for actual curve inverse pullback.
-/
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

noncomputable section
namespace MazurTransfer.DivisorSectionSpaceFieldActionHelpers20261017
open AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_image_lSpaceOn_iff (σ : F ≃ₐ[K] F) (S : Set (Place K F))
    (D : Divisor K F) (f : F) :
    σ f ∈ lSpaceOn ((fun v : Place K F => σ • v) '' S) (σ • D) ↔ f ∈ lSpaceOn S D := by
  rw [mem_lSpaceOn_iff_ord, mem_lSpaceOn_iff_ord]
  have hz : σ f = 0 ↔ f = 0 := map_eq_zero_iff σ σ.injective
  constructor
  · intro h v hv
    have H := h (σ • v) ⟨v, hv, rfl⟩
    simpa only [hz, Divisor.smul_apply_smul, Place.ord_smul] using H
  · rintro h _ ⟨v, hv, rfl⟩
    simpa only [hz, Divisor.smul_apply_smul, Place.ord_smul] using h v hv

end MazurTransfer.DivisorSectionSpaceFieldActionHelpers20261017
open MazurTransfer.DivisorSectionSpaceFieldActionHelpers20261017
open AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
theorem solution (σ : F ≃ₐ[K] F) (S : Set (Place K F)) (D : Divisor K F) :
    σ '' (lSpaceOn S D : Set F) =
      (lSpaceOn ((fun v : Place K F => σ • v) '' S) (σ • D) : Set F) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_image_lSpaceOn_iff σ S D g).mpr hg
  · intro hf
    refine ⟨σ.symm f, ?_, σ.apply_symm_apply f⟩
    apply (mem_image_lSpaceOn_iff σ S D (σ.symm f)).mp
    rw [σ.apply_symm_apply]
    exact hf

#print axioms solution
