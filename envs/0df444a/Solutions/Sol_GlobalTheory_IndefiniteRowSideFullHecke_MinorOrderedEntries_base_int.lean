-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.base_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:26.034794+00:00
-- url     : https://prove2.me/submissions/6e34ae39-cf99-4237-8684-77a3fd043517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_block_odd

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
theorem _root_.solution (Q : Entries S) : ∀ x ∈ Q.basePar, ∃ z : ℤ, x = z := by
  intro x hx
  simp only [Entries.basePar, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map] at hx
  rcases hx with ⟨i, -, rfl⟩ | ⟨j, -, rfl | h⟩
  · exact ⟨_, rfl⟩
  · exact ⟨-Q.b j, by push_cast; ring⟩
  · exact block_odd (-Q.e j) S.t_odd x (by exact_mod_cast h)
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
