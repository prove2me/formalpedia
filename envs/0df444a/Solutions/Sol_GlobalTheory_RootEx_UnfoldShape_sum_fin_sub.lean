-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.sum_fin_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:49.649247+00:00
-- url     : https://prove2.me/submissions/176845ee-ed01-4b30-a7ac-fa98abf3c689

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (c j : ℕ) (hj : j ≤ c) :
    ∑ l : Fin c, (j - (l.val + 1)) = j * (j - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => j - (l + 1)) c]
  have h1 : ∑ l ∈ Finset.range c, (j - (l + 1)) = ∑ l ∈ Finset.range j, (j - (l + 1)) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 hj) ?_
    intro x _ hx
    simp only [Finset.mem_range] at hx
    omega
  rw [h1, ← Finset.sum_range_id, ← Finset.sum_range_reflect (fun i => i) j]
  refine Finset.sum_congr rfl fun x _ => by omega
end GlobalTheory.RootEx.UnfoldShape
