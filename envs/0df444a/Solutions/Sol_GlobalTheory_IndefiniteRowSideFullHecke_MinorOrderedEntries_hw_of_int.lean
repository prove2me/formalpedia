-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:27.598113+00:00
-- url     : https://prove2.me/submissions/cbb68640-e0eb-4043-bf29-155786924757

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_exact

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
theorem _root_.solution (p : List ℚ) (hl : Odd p.length) (h : ∀ x ∈ p, ∃ z : ℤ, x = z) (i : ℕ) (hi : i < p.length) :
    (hw p i : ℚ) = p[i] - (((p.length : ℚ) - 1) / 2 - i) := by
  refine hw_exact p (fun x hx => ?_) i hi
  obtain ⟨z, rfl⟩ := h x hx
  obtain ⟨r, hr⟩ := hl
  exact ⟨z - r, by rw [hr]; push_cast; ring⟩
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
