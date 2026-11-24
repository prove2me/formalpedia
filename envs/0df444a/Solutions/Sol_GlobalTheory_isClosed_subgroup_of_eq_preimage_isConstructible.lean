-- Prove2me | solution 1 for GlobalTheory.isClosed_subgroup_of_eq_preimage_isConstructible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:26.611592+00:00
-- url     : https://prove2.me/submissions/5619c8ff-0e47-4dc3-897f-5d04d860bcb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_exists_isOpen_inter_closure_subset_of_isConstructible
import Theorems.Thm_GlobalTheory_isClosed_subgroup_of_isOpen_inter_closure_subset

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
variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [ContinuousInv G]
namespace GlobalTheory
theorem _root_.solution (H : Subgroup G) {f : G → Z}
    (hf : Continuous f) {C : Set Z} (hC : IsConstructible C) (hH : (H : Set G) = f ⁻¹' C) :
    IsClosed (H : Set G) := by
  obtain ⟨V, hV, h1, h2⟩ := exists_isOpen_inter_closure_subset_of_isConstructible hf hC
  rw [← hH] at h1 h2
  refine isClosed_subgroup_of_isOpen_inter_closure_subset H hV h1 ?_
  rw [← closure_nonempty_iff, h2]
  exact ⟨1, subset_closure H.one_mem⟩
end GlobalTheory
