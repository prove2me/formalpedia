-- Prove2me | solution 1 for GroundTheory.LocalField.openCompletion.denseRange_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:41.60983+00:00
-- url     : https://prove2.me/submissions/0cfc50e7-e610-40e8-be5a-a516fe365303

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_OpenCompletion
import Theorems.Thm_GroundTheory_LocalField_openCompletion_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
open GroundTheory.LocalField.openCompletion
variable {G}
namespace GroundTheory.LocalField.openCompletion
theorem _root_.solution : DenseRange (of G) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro a
  rw [mem_closure_iff]
  intro U hU haU
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨I, u, hu, hIV⟩ := isOpen_pi_iff.1 hV _ haU
  let H₀ : Subgroup G := ⨅ H ∈ I, (H : Subgroup G)
  have hH₀ : H₀ ∈ openFiniteIndex G := by
    refine ⟨?_, Subgroup.finiteIndex_iInf' _ fun H _ => H.2.2⟩
    have : (H₀ : Set G) = ⋂ H ∈ I, ((H : Subgroup G) : Set G) := by
      simp [H₀, Subgroup.coe_iInf]
    rw [this]
    exact isOpen_biInter_finset fun H _ => H.2.1
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
    ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) ⟨H₀, hH₀⟩)
  refine ⟨of G x, hIV fun H hH => ?_, x, rfl⟩
  have hle : H₀ ≤ (H : Subgroup G) := iInf₂_le H hH
  have := apply_eq a (H := ⟨H₀, hH₀⟩) (H' := H) hle
  rw [← hx, quotientMapOfLE_mk] at this
  change (x : G ⧸ (H : Subgroup G)) ∈ u H
  rw [this]
  exact (hu H hH).2
end GroundTheory.LocalField.openCompletion
