-- Prove2me | solution 1 for GlobalTheory.VolFin.Den.finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:14.713722+00:00
-- url     : https://prove2.me/submissions/cf59af19-64a9-4794-9a55-e6caac8737a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
import Theorems.Thm_GlobalTheory_VolFin_mem_piece
import Theorems.Thm_GlobalTheory_VolFin_mul_mem_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
namespace GlobalTheory.VolFin
namespace Den
theorem _root_.solution {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) (s : Finset F) :
    ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ u ∈ s, q * u ∈ piece R γ c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, mem_piece.2 fun i => by simp, one_ne_zero, by simp⟩
  | insert u s hu ih =>
    obtain ⟨c, q, hq, hq0, hs⟩ := ih
    obtain ⟨c', q', hq', hq'0, hu'⟩ := h u
    refine ⟨c + c', q * q', mul_mem_piece hq hq', mul_ne_zero hq0 hq'0, ?_⟩
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [mul_assoc]
      exact mul_mem_piece hq hu'
    · rw [mul_right_comm]
      exact mul_mem_piece (hs v hv) hq'
end Den
end GlobalTheory.VolFin
