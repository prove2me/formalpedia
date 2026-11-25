-- Prove2me | solution 1 for GlobalTheory.IntBall.MinorLast.n_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:54.080992+00:00
-- url     : https://prove2.me/submissions/82672d62-0168-4a51-b76f-eca7fd8c7ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLast
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_nmat_eq

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
theorem _root_.solution (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (a : Fin p) :
    mat (nFrame X z) τ (Fin.last p) a.castSucc =
      ∑ c : Fin p, lowMat (zOf X z τ) (Fin.last p) c.castSucc * lowMat (zOf X z τ) c.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ (Fin.last p) c * leviFrame X z τ c a.castSucc) = _
  simp [zFrame, leviFrame, hp, nmat_eq, Fin.sum_univ_castSucc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [if_neg (by omega)]
end GlobalTheory.IntBall.MinorLast
