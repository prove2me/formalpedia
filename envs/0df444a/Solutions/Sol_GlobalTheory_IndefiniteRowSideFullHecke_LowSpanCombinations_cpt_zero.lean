-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.cpt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:03.933262+00:00
-- url     : https://prove2.me/submissions/7c61cfa5-f6a6-4455-8cf3-3f6d1368976d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  have h : mat (nmat X 0) τ = 1 := by
    ext a b
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    split_ifs with h1 h2
    · exact absurd h2 h1.ne'
    all_goals first | rfl | simp
  simp only [cpt, rmul, h, Matrix.mul_one]
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
