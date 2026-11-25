-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.upper_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:40.831428+00:00
-- url     : https://prove2.me/submissions/a94612df-77a9-4fa6-8bbd-56fd98a26e41

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Theorems.Thm_GlobalTheory_LegendreBounds_legendre_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreBounds
theorem _root_.solution (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : 1 ≤ N) :
    (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hN0 : N ≠ 0 := by omega
  have hs : 1 ≤ (Nat.digits l N).sum := by
    have hmem := List.getLast_mem ((Nat.digits_ne_nil_iff_ne_zero (b := l) (n := N)).mpr hN0)
    have hlast := Nat.getLast_digit_ne_zero l hN0
    have := List.le_sum_of_mem hmem
    omega
  have hs' : (1 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := by exact_mod_cast hs
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  linarith
end GlobalTheory.LegendreBounds
