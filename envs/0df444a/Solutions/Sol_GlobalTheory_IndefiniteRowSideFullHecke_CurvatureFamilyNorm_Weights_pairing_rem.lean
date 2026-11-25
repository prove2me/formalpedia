-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.pairing_rem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:32.423883+00:00
-- url     : https://prove2.me/submissions/36b86549-fe06-4d91-b53f-180f2630c230

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_CurvatureFamilyNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
variable {X : Data E r} (w : Weights X)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
theorem _root_.solution (τ : X.Ψ) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) + 1 = r) :
    2 * (w.hF : ℤ) + 2 ≤ w.rem τ b - w.rem τ a := by
  have h1 := (w.plus_div τ b hb).1
  have h2 := (w.minus_div τ a ha).1
  have hp := w.shape.p0_pos
  have hq := w.shape.witt
  have e1 : de2 X τ a = -1 := by simp only [de2]; rw [if_pos (by omega)]
  have e2 : de2 X τ b = 1 := by simp only [de2]; rw [if_neg (by omega)]
  have e3 : ((b : ℕ) : ℤ) = r - 1 := by omega
  simp only [rem, Fp, L, frameWt, kapW, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e1, e2, e3, ha]
  push_cast
  nlinarith
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
