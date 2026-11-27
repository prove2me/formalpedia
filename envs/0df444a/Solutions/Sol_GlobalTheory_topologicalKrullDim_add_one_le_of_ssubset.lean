-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:59.5+00:00
-- url     : https://prove2.me/submissions/14e247ef-a4a5-4748-b1ec-9bf8a9e1bd7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimAddOneLeOfSsubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (T : Type) [TopologicalSpace T] (A B : Set T)
    (hA : IsClosed A) (hAi : IsIrreducible A) (hBi : IsIrreducible B) (hAB : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  have hsub : A ⊆ B := hAB.subset
  have hemb : Topology.IsClosedEmbedding (Set.inclusion hsub) :=
    Topology.IsClosedEmbedding.inclusion hsub (hA.preimage continuous_subtype_val)
  haveI : IrreducibleSpace A := Subtype.irreducibleSpace hAi
  haveI : IrreducibleSpace B := Subtype.irreducibleSpace hBi
  let f : IrreducibleCloseds A → IrreducibleCloseds B := fun Z =>
    ⟨Set.inclusion hsub '' (Z : Set A),
      Z.isIrreducible.image _ hemb.continuous.continuousOn,
      hemb.isClosedMap _ Z.isClosed⟩
  let top : IrreducibleCloseds B := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ B, isClosed_univ⟩
  have hf : StrictMono f := by
    intro Z W h
    have h' : (Z : Set A) ⊂ (W : Set A) := h
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.inclusion hsub '' (W : Set A)
    exact hemb.injective.injOn.image_ssubset_image_iff (Set.subset_univ _) (Set.subset_univ _) |>.mpr h'
  have htop : ∀ Z, f Z < top := by
    intro Z
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.univ
    obtain ⟨x, hxB, hxA⟩ := Set.exists_of_ssubset hAB
    refine Set.ssubset_univ_iff.mpr ?_
    intro h
    have : (⟨x, hxB⟩ : B) ∈ Set.inclusion hsub '' (Z : Set A) := h ▸ Set.mem_univ _
    obtain ⟨y, -, hy⟩ := this
    have : (y : T) = x := congrArg Subtype.val hy
    exact hxA (this ▸ y.2)
  haveI : Nonempty (IrreducibleCloseds A) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ A, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds A) → IrreducibleCloseds B := WithTop.recTopCoe top f
  have hg : StrictMono g := by
    rw [WithTop.strictMono_iff]
    exact ⟨hf, htop⟩
  have := Order.krullDim_le_of_strictMono g hg
  rwa [Order.krullDim_WithTop] at this
end GlobalTheory
