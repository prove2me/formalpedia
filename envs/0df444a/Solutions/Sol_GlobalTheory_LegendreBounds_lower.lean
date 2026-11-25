-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:05.528816+00:00
-- url     : https://prove2.me/submissions/d93ad0a4-581c-4a65-9a19-45fbabfaad0c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Theorems.Thm_GlobalTheory_LegendreBounds_digitSum_le
import Theorems.Thm_GlobalTheory_LegendreBounds_legendre_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.PGsh
namespace GlobalTheory.LegendreBounds
private theorem digits_sum_div_pred_le_log_add_one (l N : ℕ) (hl : 1 < l) :
    ((Nat.digits l N).sum : ℝ) / (l - 1) ≤ Nat.log l N + 1 := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl
    linarith
  rw [div_le_iff₀ hl1]
  have h := digitSum_le l N hl
  have h' : ((Nat.digits l N).sum : ℝ) ≤ ((Nat.log l N + 1) * (l - 1) : ℕ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hl.le, Nat.cast_one] at h'
  exact h'
private theorem natLog_le_logb_of_le (l N M : ℕ) (hl : 1 < l) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (Nat.log l N : ℝ) ≤ Real.logb l M := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.le_logb_iff_rpow_le hl' hM', Real.rpow_natCast]
  have : l ^ Nat.log l N ≤ M := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hM
    · exact (Nat.pow_log_le_self l hN.ne').trans hNM
  exact_mod_cast this
end GlobalTheory.LegendreBounds
end

set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreBounds
theorem _root_.solution (l : ℕ) (hl : l.Prime) (N M : ℕ) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (N : ℝ) / (l - 1) - (Real.logb l M + 1) ≤ padicValNat l N.factorial := by
  have h1 := digits_sum_div_pred_le_log_add_one l N hl.one_lt
  have h2 := natLog_le_logb_of_le l N M hl.one_lt hM hNM
  rw [legendre_real l hl N, sub_div]
  linarith
end GlobalTheory.LegendreBounds
