-- Prove2me | solution 1 for GlobalTheory.IntBallMinorOne.eR_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:27.801438+00:00
-- url     : https://prove2.me/submissions/96b3b528-d5c9-4086-9b5b-f9e6b29293bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eR_inl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IntBallMinorOne.eR_inl

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBallMinorOne
open Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IntBallMinorOne
theorem _root_.solution (hr : 1 ≤ r) (i : Fin (r - 1)) : ((eR r hr (Sum.inr i) : Fin r) : ℕ) = 1 + i := by
  simp [eR]
end GlobalTheory.IntBallMinorOne
