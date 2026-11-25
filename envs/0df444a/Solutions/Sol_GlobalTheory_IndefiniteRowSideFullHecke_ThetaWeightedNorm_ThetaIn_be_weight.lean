-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn.be_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:23.639809+00:00
-- url     : https://prove2.me/submissions/12957f64-0e77-4862-810f-5b194d55df74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaWeightedNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn
variable {X : Data E r} (I : ThetaIn X)
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn
theorem _root_.solution : 2 • ((I.i * I.g0h) • I.de2) + I.n1 • (2 • I.L - I.de2) = (2 * I.n1) • I.L := by
  unfold n1 g0
  module
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn
