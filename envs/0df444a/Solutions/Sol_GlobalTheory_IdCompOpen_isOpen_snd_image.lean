-- Prove2me | solution 1 for GlobalTheory.IdCompOpen.isOpen_snd_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:37:17.505846+00:00
-- url     : https://prove2.me/submissions/2dd00b39-8d00-41c3-9e63-962a1a575ced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IdCompOpen
namespace GlobalTheory.IdCompOpen
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens,
    IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hG U
  have hs : Smooth (pullback.snd G.hom G.hom) := inferInstance
  have ho : UniversallyOpen (pullback.snd G.hom G.hom) := UniversallyOpen.of_flat _
  have hmap : IsOpenMap (snd G G).left := (pullback.snd G.hom G.hom).isOpenMap
  have hW : IsOpen ((fst G G).left ⁻¹' (U : Set G.left) ∩ (μ[G]).left ⁻¹' (U : Set G.left)) :=
    ((U.isOpen.preimage (fst G G).left.continuous)).inter (U.isOpen.preimage (μ[G]).left.continuous)
  convert hmap _ hW using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨w, h1, h2, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3⟩
  · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h1, h2, h3⟩
end GlobalTheory.IdCompOpen
