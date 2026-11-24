-- Prove2me | solution 1 for GlobalTheory.finiteDimensional_span_multilinear_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:07.964709+00:00
-- url     : https://prove2.me/submissions/1528945d-41bf-47e4-a58d-c7dfe68c59e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FiniteDimensionalSpanMultilinearValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F)
      (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) →
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  have := hW
  let T' : MultilinearMap ℂ (fun i => W i) F := T.compLinearMap (fun i => (W i).subtype)
  have hset : {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v} = Set.range T' := by
    ext f
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => ⟨v i, hv i⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun i => (w i : E i), fun i => (w i).2, rfl⟩
  have hle : Submodule.span ℂ (Set.range T') ≤ LinearMap.range (PiTensorProduct.lift T') := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ w, by simp⟩
  rw [hset]
  exact Submodule.finiteDimensional_of_le hle
end GlobalTheory
