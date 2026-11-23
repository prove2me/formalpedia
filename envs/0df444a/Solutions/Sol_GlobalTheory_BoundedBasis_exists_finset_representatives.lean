-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.exists_finset_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:26.757773+00:00
-- url     : https://prove2.me/submissions/97fbd9e7-9ccd-4dce-9b6e-b6e1bc46c9ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {α β : Type*} [Finite β] (S : Set α) (f : S → β) :
    ∃ V : Finset S, V.card ≤ Nat.card β ∧ ∀ s : S, ∃ t ∈ V, f t = f s := by
  classical
  have := Fintype.ofFinite (Set.range f)
  refine ⟨Finset.univ.image fun b : Set.range f => b.2.choose, ?_, fun s => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨f s, s, rfl⟩),
      (⟨s, rfl⟩ : f s ∈ Set.range f).choose_spec⟩
end GlobalTheory.BoundedBasis
