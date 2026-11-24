-- Prove2me | solution 1 for GlobalTheory.CurvMargin.coeff_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:34.747844+00:00
-- url     : https://prove2.me/submissions/77947a1a-3857-45b3-81e7-1b96ae50fd0c

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
theorem _root_.solution (p : ℕ) {a b : ℕ} (h : b < a) (u v : ℝ) :
    (a < p ∧ sgn p a * sgn p b * (v - u) = v - u) ∨
    (p ≤ b ∧ sgn p a * sgn p b * (v - u) = v - u) ∨
    (b < p ∧ p ≤ a ∧ sgn p a * sgn p b * (v - u) = u - v) := by
  unfold sgn
  by_cases ha : a < p
  · left; refine ⟨ha, ?_⟩; rw [if_pos ha, if_pos (h.trans ha)]; ring
  · by_cases hb : b < p
    · right; right; refine ⟨hb, not_lt.1 ha, ?_⟩; rw [if_neg ha, if_pos hb]; ring
    · right; left; refine ⟨not_lt.1 hb, ?_⟩; rw [if_neg ha, if_neg hb]; ring
end GlobalTheory.CurvMargin
