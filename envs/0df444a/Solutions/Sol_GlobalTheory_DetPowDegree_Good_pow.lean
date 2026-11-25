-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.Good.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:06.817314+00:00
-- url     : https://prove2.me/submissions/b4af73a6-4cb7-46dc-a04a-4d68da005887

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
theorem _root_.solution {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p) (k : ℕ) :
    Good l L E (n * k) (d * k) (s * k) (p ^ k) := by
  induction k with
  | zero => simpa using Good.C (α := α) (l := l) (L := L) (E := E) 1
  | succ k ih => rw [pow_succ]; simpa only [mul_add, mul_one] using ih.mul hp
end Good
end GlobalTheory.DetPowDegree
