-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.vadd_killed_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:32.820254+00:00
-- url     : https://prove2.me/submissions/cb8c21cd-b2d3-4ff2-8d84-8197ba42c283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_iff_mem_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] (I : Finset (ZMod d)) {x : ZMod d} (hx : x ∈ I) :
    x +ᵥ killed d (Nat.card (AddAction.stabilizer (ZMod d) I)) ⊆ I := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_vadd_finset.mp hy
  have hz' : z +ᵥ I = I := (mem_iff_mem_killed _ z).mpr hz
  have : z +ᵥ x ∈ z +ᵥ I := Finset.vadd_mem_vadd_finset hx
  rw [hz'] at this
  simpa [add_comm] using this
end GlobalTheory.PeriodDvd
