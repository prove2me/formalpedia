-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.padicValNat_prod_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:39.603286+00:00
-- url     : https://prove2.me/submissions/2033c941-4006-4a8f-965a-aee7d40ce9ca

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) {κ : Type} (s : Finset κ)
    (A : κ → ℕ) :
    (padicValNat l (∏ j ∈ s, (A j).factorial) : ℝ)
      = ∑ j ∈ s, (padicValNat l (A j).factorial : ℝ) := by
  have := Fact.mk hl
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _), Nat.cast_add, ih]
end GlobalTheory.LegendreBounds
