-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:17.06385+00:00
-- url     : https://prove2.me/submissions/31399308-b4a8-40ce-ae09-4350aacc9224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes

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
    {d : WithBot ℕ∞} (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro T
  obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, hd⟩ := h x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hU.isOpenEmbedding_subtypeVal
  obtain ⟨T', hT'⟩ := e.surjective ⟨T, ⟨x, hxU⟩, hx⟩
  have : IrreducibleCloseds.map _ hU.isOpenEmbedding_subtypeVal.continuous T' = T :=
    congr($(hT').1)
  rw [← this, hU.isOpenEmbedding_subtypeVal.coheight_map]
  exact (Order.coheight_le_krullDim T').trans hd
end GlobalTheory
