-- Prove2me | solution 1 for GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:28.274733+00:00
-- url     : https://prove2.me/submissions/6fd06697-7d71-4841-b26c-385ef11c12a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_interior_frontier_preimage_of_isConstructible
import Theorems.Thm_GlobalTheory_dense_interior_of_interior_frontier_eq_empty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
namespace GlobalTheory
theorem _root_.solution {f : Y → Z} (hf : Continuous f)
    {C : Set Z} (hC : IsConstructible C) :
    ∃ V : Set Y, IsOpen V ∧ V ∩ closure (f ⁻¹' C) ⊆ f ⁻¹' C ∧
      closure (V ∩ closure (f ⁻¹' C)) = closure (f ⁻¹' C) := by
  set S := f ⁻¹' C with hS
  have h1 := interior_frontier_preimage_of_isConstructible
    (hf.comp (continuous_subtype_val (p := fun y => y ∈ closure S))) hC
  rw [Set.preimage_comp, ← hS] at h1
  have hd : Dense ((↑) ⁻¹' S : Set (closure S)) := by
    rw [Subtype.dense_iff]
    refine closure_mono ?_
    intro y hy
    exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
  have h2 := dense_interior_of_interior_frontier_eq_empty hd h1
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1
    (isOpen_interior (s := ((↑) ⁻¹' S : Set (closure S))))
  refine ⟨V, hV, ?_, ?_⟩
  · rintro y ⟨hyV, hyS⟩
    have : (⟨y, hyS⟩ : closure S) ∈ interior ((↑) ⁻¹' S : Set (closure S)) := hVe ▸ hyV
    exact interior_subset (s := ((↑) ⁻¹' S : Set (closure S))) this
  · refine Set.Subset.antisymm (closure_minimal Set.inter_subset_right isClosed_closure) ?_
    rw [Subtype.dense_iff, ← hVe, Subtype.image_preimage_coe, Set.inter_comm] at h2
    exact h2
end GlobalTheory
