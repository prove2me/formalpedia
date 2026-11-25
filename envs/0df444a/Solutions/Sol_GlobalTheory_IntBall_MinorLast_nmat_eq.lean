-- Prove2me | solution 1 for GlobalTheory.IntBall.MinorLast.nmat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:48:56.685664+00:00
-- url     : https://prove2.me/submissions/f835bda8-8a16-47ca-854f-a6b05bcf9655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLast

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
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.MinorLast
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {p : ℕ} (X : Data E (p + 1))
namespace GlobalTheory.IntBall.MinorLast
theorem _root_.solution (z : V (nd X)) (τ : X.Ψ) (a b : Fin (p + 1)) :
    nmat X z τ a b = lowMat (zOf X z τ) a b := rfl
end GlobalTheory.IntBall.MinorLast
