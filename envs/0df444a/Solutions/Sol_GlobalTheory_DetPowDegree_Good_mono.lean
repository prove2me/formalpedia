-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.Good.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:04.199165+00:00
-- url     : https://prove2.me/submissions/d5abcf89-6f20-43f3-966b-a2df31ebd02d

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
theorem _root_.solution {n n' d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (h : Good l L E n d s p)
    (hn : n ≤ n') : Good l L E n' d s p :=
  fun m hm => ⟨(h m hm).1.trans hn, (h m hm).2⟩
end Good
end GlobalTheory.DetPowDegree
