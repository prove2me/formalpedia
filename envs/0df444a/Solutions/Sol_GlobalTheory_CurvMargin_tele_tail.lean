-- Prove2me | solution 1 for GlobalTheory.CurvMargin.tele_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:35.816886+00:00
-- url     : https://prove2.me/submissions/4951d213-18dd-436f-9d7e-58e3c090de5d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.CurvMargin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CurvMargin
theorem _root_.solution (L : ℕ → ℝ) (p : ℕ) : ∀ r : ℕ, p ≤ r →
    ∑ i ∈ Finset.range r, (if i < p then (0 : ℝ) else 1) * (L (i + 1) - L i) = L r - L p := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_pos (Finset.mem_range.1 hi), zero_mul]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_neg (not_lt.2 hn)]
    ring
end GlobalTheory.CurvMargin
