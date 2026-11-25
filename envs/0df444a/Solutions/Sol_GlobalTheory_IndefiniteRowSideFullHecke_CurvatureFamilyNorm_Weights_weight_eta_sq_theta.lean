-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.weight_eta_sq_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:03.688604+00:00
-- url     : https://prove2.me/submissions/f8f31711-0737-4de0-b8cc-98baf2d23de4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_CurvatureFamilyNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
variable {X : Data E r} (w : Weights X)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
theorem _root_.solution : (2 : ℤ) • w.wEt + (w.n₁ : ℤ) • w.twoG₁ = (2 * (w.n₁ : ℤ)) • w.L := by
  funext τ a
  simp only [wEt, twoG₁, frameWt, n₁, g0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  push_cast
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
