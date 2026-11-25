-- Prove2me | solution 1 for GlobalTheory.IntBall.MinorLast.n_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:58.452366+00:00
-- url     : https://prove2.me/submissions/ea7a2918-8354-4ea5-b5cc-543b27c28f19

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
theorem _root_.solution (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (i a : Fin p) :
    mat (nFrame X z) τ i.castSucc a.castSucc = lowMat (zOf X z τ) i.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ i.castSucc c * leviFrame X z τ c a.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  have hl : zFrame X z τ i.castSucc (Fin.last p) = 0 := by
    simp [zFrame, hp, Fin.ext_iff]; omega
  rw [hl, zero_mul, add_zero]
  rw [Finset.sum_eq_single i]
  · simp [zFrame, leviFrame, hp, nmat_eq]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro b _ hb
    have : i.castSucc ≠ b.castSucc := fun h => hb (Fin.castSucc_injective _ h).symm
    simp [zFrame, hp, this]
  · simp
end GlobalTheory.IntBall.MinorLast
