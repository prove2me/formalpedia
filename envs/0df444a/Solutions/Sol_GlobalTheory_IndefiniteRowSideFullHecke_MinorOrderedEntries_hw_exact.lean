-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:16.690828+00:00
-- url     : https://prove2.me/submissions/5073eef3-5894-4caa-be23-6039bbcfb735

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
theorem _root_.solution (p : List ℚ) (h : ∀ x ∈ p, ∃ z : ℤ, x = z + ((p.length : ℚ) - 1) / 2) (i : ℕ) (hi : i < p.length) :
    (hw p i : ℚ) = p[i] - (((p.length : ℚ) - 1) / 2 - i) := by
  obtain ⟨z, hz⟩ := h _ (List.getElem_mem hi)
  have : p.getD i 0 - (((p.length : ℚ) - 1) / 2 - i) = ((z + i : ℤ) : ℚ) := by
    rw [List.getD_eq_getElem _ _ hi, hz]; push_cast; ring
  rw [hw, this, Int.floor_intCast, hz]; push_cast; ring
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
