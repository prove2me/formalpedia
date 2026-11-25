-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:59.731662+00:00
-- url     : https://prove2.me/submissions/837b350d-fd03-4052-b39e-5ba37e5ae9a4

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) ≤ (N : ℝ) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  have : (0 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := Nat.cast_nonneg _
  linarith
end GlobalTheory.LegendreBounds
