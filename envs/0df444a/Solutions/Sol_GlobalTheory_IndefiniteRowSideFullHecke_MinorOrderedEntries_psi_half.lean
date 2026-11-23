-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.psi_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:28.150491+00:00
-- url     : https://prove2.me/submissions/f40b1099-f157-4f9b-a241-1e9763accc2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_block_even

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
theorem _root_.solution (Q : Entries S) (hQ : Q.Good) : ∀ x ∈ Q.psiPar, ∃ z : ℤ, x = z + 1 / 2 := by
  have hs : Even (S.s - 1) := by obtain ⟨r, hr⟩ := S.s_odd; exact ⟨r, by omega⟩
  intro x hx
  simp only [Entries.psiPar, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | ⟨i, -, h | rfl⟩ | ⟨i, -, rfl⟩
  exacts [hQ.a_half _, block_even _ hs x h, hQ.a_half _, hQ.u_half _]
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
