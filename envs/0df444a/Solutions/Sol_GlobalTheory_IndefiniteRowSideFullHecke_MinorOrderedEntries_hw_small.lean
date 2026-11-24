-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:39:59.563911+00:00
-- url     : https://prove2.me/submissions/66e2b983-6c52-4b62-9e20-1d1e89cf6d04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_small
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_block_odd
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_of_int
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_odd_nC
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_base_int

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
theorem _root_.solution (Q : Entries S) (i : ℕ) (hi : i < Q.smallPar.length) :
    (hw Q.smallPar i : ℚ) = Q.smallPar[i] - (((Q.smallPar.length : ℚ) - 1) / 2 - i) := by
  refine hw_of_int _ (length_small Q ▸ odd_nC S.m_even) (fun x hx => ?_) i hi
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨j, -, h⟩ := List.mem_flatMap.1 h
    exact block_odd (Q.c j) S.s_odd x h
  · exact base_int Q x h
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
