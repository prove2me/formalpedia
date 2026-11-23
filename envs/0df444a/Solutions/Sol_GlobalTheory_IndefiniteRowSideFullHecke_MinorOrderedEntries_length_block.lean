-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:53.112582+00:00
-- url     : https://prove2.me/submissions/9ae14d6f-36ae-4fa7-8f56-1c11ebe0939c

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
theorem _root_.solution (x : ℚ) (n : ℕ) : (block x n).length = n := by simp [block]
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
