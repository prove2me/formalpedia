-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.pairing_kapW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:49.853715+00:00
-- url     : https://prove2.me/submissions/c565e7f2-0340-472c-ad5a-d5ab66ddf3fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FundamentalSetFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
theorem _root_.solution (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) (τ : X.Ψ) :
    pairing X h0 h1 (kapW X) τ = 2 * (r : ℤ) - 2 := by
  have : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  simp only [pairing, kapW, this]
  push_cast
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
