-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.Good.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:05.086911+00:00
-- url     : https://prove2.me/submissions/65ff7e3d-e76e-4748-87df-ac2ab0999915

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
theorem _root_.solution {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p) :
    Good l L E n d s (-p) := by
  intro m hm
  rw [coeff_neg] at hm ⊢
  have h : coeff m p ≠ 0 := by simpa using hm
  exact ⟨(hp m h).1, (hp m h).2.1, (hp m h).2.2.neg_right⟩
end Good
end GlobalTheory.DetPowDegree
