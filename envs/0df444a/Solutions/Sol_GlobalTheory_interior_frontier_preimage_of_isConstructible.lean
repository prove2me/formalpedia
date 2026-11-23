-- Prove2me | solution 1 for GlobalTheory.interior_frontier_preimage_of_isConstructible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:34.889742+00:00
-- url     : https://prove2.me/submissions/61141a29-4be6-4bba-aaba-03069cddbd41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

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
    {C : Set Z} (hC : IsConstructible C) : interior (frontier (f ⁻¹' C)) = ∅ := by
  induction hC using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    rw [← frontier_compl]
    exact interior_frontier (hU.preimage hf).isClosed_compl
  | union s _ t _ hs ht =>
    rw [Set.preimage_union]
    have h1 : frontier (f ⁻¹' s ∪ f ⁻¹' t) ⊆ frontier (f ⁻¹' s) ∪ frontier (f ⁻¹' t) :=
      (frontier_union_subset _ _).trans
        (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)
    have h2 : interior (frontier (f ⁻¹' s) ∪ frontier (f ⁻¹' t)) = ∅ := by
      rw [interior_union_isClosed_of_interior_empty isClosed_frontier ht, hs]
    exact Set.eq_empty_of_subset_empty (h2 ▸ interior_mono h1)
  | compl s _ hs => rw [Set.preimage_compl, frontier_compl, hs]
end GlobalTheory
