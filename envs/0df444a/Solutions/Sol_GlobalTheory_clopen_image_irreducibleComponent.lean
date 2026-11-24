-- Prove2me | solution 1 for GlobalTheory.clopen_image_irreducibleComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:13.3678+00:00
-- url     : https://prove2.me/submissions/be6cccc0-e07d-4cbc-8811-984de0cbb715

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComponentSurjectsClopen

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
theorem _root_.solution : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  intro A B _ _ f hf hop hcl hcomp S hS hSc a ha
  refine ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a,
    mem_irreducibleComponent, ?_⟩
  have hCc : IsClosed (irreducibleComponent a) := isClosed_irreducibleComponent
  have hCo : IsOpen (irreducibleComponent a) :=
    hcomp _ (irreducibleComponent_mem_irreducibleComponents a)
  have hCp : IsPreconnected (irreducibleComponent a) :=
    (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := a))).isPreconnected
  have hsub : irreducibleComponent a ⊆ f ⁻¹' S :=
    hCp.subset_isClopen (hS.preimage hf) ⟨a, mem_irreducibleComponent, ha⟩
  have himg : f '' irreducibleComponent a ⊆ S := Set.image_subset_iff.mpr hsub
  have hclo : IsClopen (f '' irreducibleComponent a) := ⟨hcl _ hCc, hop _ hCo⟩
  refine le_antisymm himg ?_
  exact hSc.subset_isClopen hclo ⟨f a, ha, a, mem_irreducibleComponent, rfl⟩
end GlobalTheory
