-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.Good.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:55.07319+00:00
-- url     : https://prove2.me/submissions/f4f10bc1-6173-4cbe-bda1-a1cfde217c72

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_neg

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
theorem _root_.solution {n d s : ℕ} {p q : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p)
    (hq : Good l L E n d s q) : Good l L E n d s (p - q) := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg
end Good
end GlobalTheory.DetPowDegree
