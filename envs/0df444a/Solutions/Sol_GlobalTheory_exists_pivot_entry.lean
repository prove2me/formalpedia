-- Prove2me | solution 1 for GlobalTheory.exists_pivot_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:50.419966+00:00
-- url     : https://prove2.me/submissions/596c6c7f-e7d8-4b8e-ab11-bfba286fbd1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIntegralPivotDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ}
    (w : Fin n → L) (hw : w ≠ 0) : ∃ k, w k ≠ 0 ∧ ∀ i, w i / w k ∈ W := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    exact hw (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i => W.valuation (w i)) ⟨j, Finset.mem_univ j⟩
  have hwk : w k ≠ 0 := by
    intro h0
    have hle := hk j (Finset.mem_univ j)
    rw [h0, map_zero] at hle
    exact hj ((Valuation.zero_iff _).1 (le_antisymm hle zero_le))
  refine ⟨k, hwk, fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ i)) zero_le
end GlobalTheory
