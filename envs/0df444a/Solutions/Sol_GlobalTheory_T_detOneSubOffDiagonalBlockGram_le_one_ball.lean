-- Prove2me | solution 1 for GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:24.233818+00:00
-- url     : https://prove2.me/submissions/4f4c8f17-10d3-4a9b-8c81-ba15986e1c9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBall
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBallStatement
import Theorems.Thm_GlobalTheory_IntBall_zDet_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  first | exact @GlobalTheory.IntBall.zDet_le_one | exact GlobalTheory.IntBall.zDet_le_one | (intros; apply GlobalTheory.IntBall.zDet_le_one <;> assumption)
end _root_.GlobalTheory.T
