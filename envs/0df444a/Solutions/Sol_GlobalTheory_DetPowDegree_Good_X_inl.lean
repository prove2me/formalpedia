-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.Good.X_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:03.338881+00:00
-- url     : https://prove2.me/submissions/08e6aa70-7be0-45d3-abcd-11db776bbe5f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowDegree
variable {α : Type} [Fintype α]
variable {l : ℤ} {L E : ℕ}
namespace GlobalTheory.DetPowDegree
namespace Good
theorem _root_.solution (a : α) : Good l L E 0 1 0 (X (Sum.inl a) : MvPolynomial (α ⊕ α) ℤ) := by
  classical
  intro m hm
  rw [coeff_X'] at hm
  have h : Finsupp.single (Sum.inl a) 1 = m := by
    by_contra h
    simp [h] at hm
  subst h
  simp [Finsupp.single_apply]
end Good
end GlobalTheory.DetPowDegree
