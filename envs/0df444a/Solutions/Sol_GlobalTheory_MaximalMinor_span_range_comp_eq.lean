-- Prove2me | solution 1 for GlobalTheory.MaximalMinor.span_range_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:02:20.414099+00:00
-- url     : https://prove2.me/submissions/0f4b692d-f01d-4184-ac56-fa459a99c4ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors
import Theorems.Thm_GlobalTheory_MaximalMinor_mem_span_of_det_update_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule Function
open GlobalTheory
open GlobalTheory.MaximalMinor
variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MaximalMinor
theorem _root_.solution (b : Basis ι R F) (G : κ → F) {σ : ι → κ}
    (hσ : b.det (G ∘ σ) ∈ nonZeroDivisors R)
    (h : ∀ τ : ι → κ, b.det (G ∘ τ) ∈ span A {b.det (G ∘ σ)}) :
    span A (Set.range (G ∘ σ)) = span A (Set.range G) := by
  refine le_antisymm (span_mono (Set.range_comp_subset_range _ _)) (span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine mem_span_of_det_update_mem b hσ fun i => ?_
  rw [← comp_update]
  exact h _
end GlobalTheory.MaximalMinor
