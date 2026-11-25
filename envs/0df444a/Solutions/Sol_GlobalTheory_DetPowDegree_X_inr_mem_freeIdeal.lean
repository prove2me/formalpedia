-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.X_inr_mem_freeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:07.594254+00:00
-- url     : https://prove2.me/submissions/ca63c360-ca78-4e34-9540-bdfc536b8cdf

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
theorem _root_.solution (a : α) :
    (X (Sum.inr a) : MvPolynomial (α ⊕ α) ℤ) ∈ freeIdeal α l := by
  classical
  intro m hm
  rw [coeff_X']
  split_ifs with h
  · subst h
    simp [Finsupp.single_apply] at hm
  · simp
end GlobalTheory.DetPowDegree
