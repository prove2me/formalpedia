-- Prove2me | solution 1 for GlobalTheory.HilbTensorExists.exists_complete_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:49.372226+00:00
-- url     : https://prove2.me/submissions/9822c321-7ca4-45c7-b527-d8a3d47f98df

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCompleteDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.HilbTensorExists
namespace GlobalTheory.HilbTensorExists
theorem _root_.solution {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by
  let V := Submodule.span ℂ (Set.range t)
  let u : X → V := fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩
  · rw [UniformSpace.Completion.inner_coe]
    rfl
  · refine UniformSpace.Completion.denseRange_coe.mono ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ (Set.range u) := hu ▸ Submodule.mem_top
    have hm := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm
end GlobalTheory.HilbTensorExists
