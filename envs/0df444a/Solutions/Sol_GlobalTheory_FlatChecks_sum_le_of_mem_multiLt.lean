-- Prove2me | solution 1 for GlobalTheory.FlatChecks.sum_le_of_mem_multiLt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:09.257012+00:00
-- url     : https://prove2.me/submissions/2c748a1f-d772-4604-a950-2d033cb90a26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlatChecks
theorem _root_.solution {n a0 T : ℕ} (h : a0 ≤ T + 1) {α : Fin n → ℕ}
    (hα : α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt n a0) : (∑ q, α q) + (T - ∑ q, α q) = T := by
  simp only [ReciprocityTheory.ChartRestriction.G.AR.multiLt, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple] at hα
  obtain ⟨d, hd, hs⟩ := hα
  omega
end GlobalTheory.FlatChecks
