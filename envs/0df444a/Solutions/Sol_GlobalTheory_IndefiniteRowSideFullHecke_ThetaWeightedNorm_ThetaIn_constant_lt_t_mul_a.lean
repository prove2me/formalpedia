-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn.constant_lt_t_mul_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:04.629144+00:00
-- url     : https://prove2.me/submissions/c8340319-87f9-4f59-9136-b44c9dca0394

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
theorem _root_.solution : I.c1 < I.t * I.a1 := by
  have h := I.frame_theta_weight_pos
  have : I.t * I.a1 = I.a1 + I.c1 := by
    unfold t
    field_simp
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.ThetaIn
