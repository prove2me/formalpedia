-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:52.970288+00:00
-- url     : https://prove2.me/submissions/3dd25ee7-75c6-4772-9e08-241a2f9352af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped TensorProduct Kronecker
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Sizes} (P : ι → Entries S)
namespace GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
theorem _root_.solution (c : ℤ) {n : ℕ} (hn : Odd n) : ∀ x ∈ block c n, ∃ z : ℤ, x = z := by
  obtain ⟨r, rfl⟩ := hn
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact ⟨c + r - i, by push_cast; ring⟩
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
