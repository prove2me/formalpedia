-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:35.014+00:00
-- url     : https://prove2.me/submissions/40b624bc-53e9-49d8-929f-28836559a134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_block
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_psi

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
theorem _root_.solution (Q : Entries S) : Q.bigPar.length = S.nR S.m := by
  have := length_psi Q
  simp [Entries.bigPar, List.length_flatMap, length_block, Sizes.nR] at this ⊢
  omega
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
