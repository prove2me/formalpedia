-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.t_mul_r_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:39.943058+00:00
-- url     : https://prove2.me/submissions/a30ae049-c858-4b55-b7da-7009f8665437

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
theorem _root_.solution : w.t * r ≤ 2 * w.T := by
  have hrd : 1 ≤ rd X := by
    apply Real.one_le_rpow _ (by positivity)
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast this
  have hr : (r : ℝ) ≤ w.T := by exact_mod_cast (by have := w.T_cols; omega : r ≤ w.T)
  have hT : (0 : ℝ) ≤ w.T := by positivity
  have hc := w.c_pos
  have hRR : rd X ^ 2 ≤ RR X := pow_le_pow_right₀ hrd (by norm_num)
  have hR0 : 0 ≤ RR X := by unfold RR; positivity
  have key : w.c1 / a1 X * r ≤ w.T := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h0 | h0
    · simp [a1, h0]
    · have hf : (0 : ℝ) < X.Ψ.card := by exact_mod_cast h0
      have e : w.c1 / a1 X * r =
          ((g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X * w.c) * rd X ^ 2 * w.T := by
        simp only [c1, a1, dp, g0, g0half]
        push_cast
        field_simp
        ring
      have h2 : ((g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X * w.c) * rd X ^ 2 ≤ 1 := by
        refine le_trans (mul_le_mul_of_nonneg_left hRR (by positivity)) (le_trans (le_of_eq ?_) w.cRR)
        ring
      rw [e]
      nlinarith
  simp only [t]
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
