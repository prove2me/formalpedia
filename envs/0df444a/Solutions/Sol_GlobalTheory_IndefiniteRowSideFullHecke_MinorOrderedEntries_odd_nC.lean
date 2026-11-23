-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.odd_nC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:17.381832+00:00
-- url     : https://prove2.me/submissions/286b9d45-49c1-4ae5-ac76-96933c9600bb

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
theorem _root_.solution {i : ℕ} (hi : Even i) : Odd (S.nC i) := by
  have hk := S.k_pos
  have h1 : Odd (S.k + S.m - 1) := by
    obtain ⟨a, ha⟩ := S.k_even.add S.m_even
    exact ⟨a - 1, by omega⟩
  exact (h1.add_even (S.m_even.mul_right _)).add_even (hi.mul_right _)
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
