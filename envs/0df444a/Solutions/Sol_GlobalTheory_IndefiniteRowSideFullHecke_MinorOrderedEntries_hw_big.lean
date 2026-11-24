-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.315072+00:00
-- url     : https://prove2.me/submissions/d4b90173-60c2-49a4-89ac-4ae6c698b5f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_big
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_block_even
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_of_half
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_even_nR
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_psi_half

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
theorem _root_.solution (Q : Entries S) (hQ : Q.Good) (i : ℕ) (hi : i < Q.bigPar.length) :
    (hw Q.bigPar i : ℚ) = Q.bigPar[i] - (((Q.bigPar.length : ℚ) - 1) / 2 - i) := by
  refine hw_of_half _ (length_big Q ▸ even_nR _) (fun x hx => ?_) i hi
  rcases List.mem_append.1 hx with h | h
  · exact psi_half Q hQ x h
  · obtain ⟨j, -, h⟩ := List.mem_flatMap.1 h
    exact block_even (-Q.e j) S.t_odd.add_one x (by exact_mod_cast h)
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
