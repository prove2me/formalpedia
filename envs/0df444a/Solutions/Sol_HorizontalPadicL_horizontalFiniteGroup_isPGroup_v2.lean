-- Prove2me | solution 1 for HorizontalPadicL.horizontalFiniteGroup_isPGroup_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T11:42:16.797394+00:00
-- url     : https://prove2.me/submissions/471fd3be-558e-4955-a191-c8550a5088cb

import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Every finite horizontal quotient is a finite `p`-group. -/
theorem _root_.solution
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ) :
    IsPGroup p (HorizontalFiniteGroup p m A) := by
  rw [IsPGroup.iff_card]
  refine ⟨∑ i : {n : ℕ // n ∈ A}, m i.1, ?_⟩
  simp [HorizontalFiniteGroup, ← Finset.prod_pow_eq_pow_sum]

end HorizontalPadicL
