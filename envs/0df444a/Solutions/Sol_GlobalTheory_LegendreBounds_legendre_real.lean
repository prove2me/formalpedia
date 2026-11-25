-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.legendre_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:33.820602+00:00
-- url     : https://prove2.me/submissions/0c080cb1-04ed-43ba-a53c-e00a7a6e38f8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) = ((N : ℝ) - ((Nat.digits l N).sum : ℕ)) / (l - 1) := by
  have := Fact.mk hl
  have h1 : (l - 1) * padicValNat l N.factorial = N - (Nat.digits l N).sum :=
    sub_one_mul_padicValNat_factorial N
  have h2 : (Nat.digits l N).sum ≤ N := Nat.digit_sum_le l N
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have h3 := congrArg (Nat.cast : ℕ → ℝ) h1
  rw [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_sub h2, Nat.cast_one] at h3
  rw [eq_div_iff (by linarith)]
  linear_combination h3
end GlobalTheory.LegendreBounds
