-- Prove2me | solution 1 for GroundTheory.Global.discreteTopology_of_isOpen_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:50.889171+00:00
-- url     : https://prove2.me/submissions/66062843-b700-42b4-ba68-f32c0d707563

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
namespace GroundTheory.Global
theorem _root_.solution {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U)
    (hH : ∀ x ∈ H, x ∈ U → x = 0) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtype_val
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have hx0 : x = 0 := by simpa using congrArg Subtype.val h
    rw [hx0]
    exact h0
  · intro h
    exact Subtype.ext (hH x hx h)
end GroundTheory.Global
