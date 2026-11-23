-- Prove2me | solution 1 for GlobalTheory.RandomTops.prod_alternate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:44.411496+00:00
-- url     : https://prove2.me/submissions/f0fe77f5-f482-4c7c-ad75-d960ace4d651

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (a b : ℝ) (m : ℕ) :
    ∏ c ∈ Finset.range (2 * m + 1), (if Even c then a else b) = a ^ (m + 1) * b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    have h2 : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      if_neg h1, if_pos h2]
    ring
end GlobalTheory.RandomTops
