-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:59:13.665836+00:00
-- url     : https://prove2.me/submissions/f8c54f7c-88cc-421f-9e60-7576a2e4d905

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_base
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
theorem _root_.solution (Q : Entries S) (i : ℕ) (hi : i < Q.basePar.length) :
    (hw Q.basePar i : ℚ) = Q.basePar[i] - (((Q.basePar.length : ℚ) - 1) / 2 - i) :=
  hw_of_int _ (length_base Q ▸ odd_nC ⟨0, rfl⟩) (base_int Q) i hi
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
