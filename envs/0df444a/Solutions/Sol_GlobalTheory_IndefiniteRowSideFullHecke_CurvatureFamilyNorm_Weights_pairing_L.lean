-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.pairing_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:50:40.925879+00:00
-- url     : https://prove2.me/submissions/f279664d-11ad-4228-98d5-c78ab4289256

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
    38 * (w.T : ℤ) ≤ 10 * (w.L τ b - w.L τ a) := by
  have h1 := (w.plus_div τ b hb).2
  have h2 := (w.minus_div τ a ha).2
  have h3 := w.plus_big τ b hb
  have h4 := w.minus_big τ a ha
  have hp := w.shape.p0_pos
  have hq := w.shape.witt
  have h5 : ((nd X : ℤ) + 2) * (2 * w.hW) + 2 * r ≤ w.T := by exact_mod_cast w.T_cols
  have h6 : 40 * ((nd X : ℤ) + 2) ≤ w.T := by exact_mod_cast w.T_forty
  have hD : (0 : ℤ) ≤ nd X := by positivity
  have hh : (0 : ℤ) ≤ w.hW := by positivity
  have e1 : de2 X τ a = -1 := by simp only [de2]; rw [if_pos (by omega)]
  have e2 : de2 X τ b = 1 := by simp only [de2]; rw [if_neg (by omega)]
  have key : ∀ u : ℤ, 2 * (w.T : ℤ) ^ 2 - w.T < ((w.T : ℤ) + nd X + 2) * (u + 1) → 19 * (w.T : ℤ) ≤ 10 * u := by
    intro u hu
    by_contra hc
    have hc' : 10 * (u + 1) ≤ 19 * (w.T : ℤ) + 9 := by omega
    have : ((w.T : ℤ) + nd X + 2) * (10 * (u + 1)) ≤ ((w.T : ℤ) + nd X + 2) * (19 * w.T + 9) :=
      mul_le_mul_of_nonneg_left hc' (by positivity)
    nlinarith
  have k1 := key (w.aW τ b) (by nlinarith)
  have k2 := key (-w.aW τ a) (by nlinarith)
  simp only [L, frameWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2]
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
