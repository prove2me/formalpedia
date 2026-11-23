-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:10.782271+00:00
-- url     : https://prove2.me/submissions/19cd0a4e-591c-42eb-ab45-7736b051a1eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
import Theorems.Thm_GlobalTheory_topologicalKrullDim_le_of_forall_exists_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open Topology TopologicalSpace
namespace GlobalTheory
theorem _root_.solution {X : Type*} [TopologicalSpace X]
    {Z : Set X} (hZ : Z.Nonempty) {d : WithBot ℕ∞}
    (h : ∀ x ∈ Z, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim (U ∩ Z : Set X) = d) :
    topologicalKrullDim Z = d := by
  have key (U : Set X) : topologicalKrullDim (U ∩ Z : Set X) =
      topologicalKrullDim (Subtype.val ⁻¹' U : Set Z) :=
    topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
      (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])
  apply le_antisymm
  · refine topologicalKrullDim_le_of_forall_exists_isOpen fun x ↦ ?_
    obtain ⟨U, hU, hxU, hd⟩ := h x x.2
    exact ⟨_, hU.preimage continuous_subtype_val, hxU, ((key U).symm.trans hd).le⟩
  · obtain ⟨x, hx⟩ := hZ
    obtain ⟨U, -, -, hd⟩ := h x hx
    rw [← hd, key]
    exact topologicalKrullDim_subspace_le _ _
end GlobalTheory
