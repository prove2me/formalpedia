-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.weight_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:07.493918+00:00
-- url     : https://prove2.me/submissions/b8e42d0e-8b6b-4064-8b6a-8413ff1c0a9b

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
theorem _root_.solution : (2 * (w.n₁ : ℤ)) • (w.ka + w.G₂) + (2 * (w.n₁ : ℤ)) • w.twoG₁ + (4 : ℤ) • w.wEt =
    (2 * (w.n₁ : ℤ) * (w.T + nd X + 6)) • w.L := by
  funext τ a
  simp only [wEt, twoG₁, ka, G₂, n₁, g0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [frameWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  push_cast
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
