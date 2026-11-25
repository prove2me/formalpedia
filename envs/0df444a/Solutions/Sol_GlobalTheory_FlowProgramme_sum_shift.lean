-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:21.947782+00:00
-- url     : https://prove2.me/submissions/efc57b9d-667f-43de-a225-49f78b810b61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - i) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)
end GlobalTheory.FlowProgramme
