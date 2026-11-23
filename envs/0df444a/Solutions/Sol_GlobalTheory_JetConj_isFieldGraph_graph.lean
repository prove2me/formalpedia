-- Prove2me | solution 1 for GlobalTheory.JetConj.isFieldGraph_graph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:08.709812+00:00
-- url     : https://prove2.me/submissions/deeb43be-f95c-4bdf-9cb7-25097d0ec7b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_mem_graph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
namespace GlobalTheory.JetConj
theorem _root_.solution (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : IsFieldGraph (graph M ρ) := by
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · obtain ⟨h, rfl⟩ := mem_graph.1 hab
    rw [map_eq_zero]
    exact ⟨fun ha => Subtype.ext ha, fun h0 => congrArg Subtype.val h0⟩
  · obtain ⟨h, rfl⟩ := mem_graph.1 hab
    refine mem_graph.2 ⟨inv_mem h, ?_⟩
    rw [← map_inv₀]
    rfl
end GlobalTheory.JetConj
