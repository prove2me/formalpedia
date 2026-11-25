-- Prove2me | solution 1 for GlobalTheory.IntBallMinorOne.eC_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:31.281278+00:00
-- url     : https://prove2.me/submissions/26532faa-8fed-45ed-afd3-f531ba324218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eR_inl
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eR_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IntBallMinorOne.eR_inl
attribute [local simp] GlobalTheory.IntBallMinorOne.eR_inr

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBallMinorOne
open Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IntBallMinorOne
theorem _root_.solution (k : ℕ) (i : Fin 1) : ((eC k (Sum.inl i) : Fin (k + 1)) : ℕ) = i := by
  simp [eC]
end GlobalTheory.IntBallMinorOne
