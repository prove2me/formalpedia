-- Prove2me | solution 1 for GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:52.568526+00:00
-- url     : https://prove2.me/submissions/a3f1b447-2afc-484c-aee3-b17917852bca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLast
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLastStatement
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_zDet_mul_colGram_le_dmin


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  first | exact @GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | exact GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | (intros; apply GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin <;> assumption)
end _root_.GlobalTheory.T
