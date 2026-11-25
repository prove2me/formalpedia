-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.Good.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:06.043992+00:00
-- url     : https://prove2.me/submissions/38d1e8b9-7b34-4caf-884b-3df41e9e6e18

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
theorem _root_.solution {n d : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d 0 p)
    (h : p ∈ freeIdeal α l) : Good l L E n d 1 p := by
  intro m hm
  refine ⟨(hp m hm).1, (hp m hm).2.1, ?_⟩
  by_cases h0 : (∑ q, m (Sum.inr q)) = 0
  · simpa [h0] using h m h0
  · have h1 : 1 - (∑ q, m (Sum.inr q)) = 0 - (∑ q, m (Sum.inr q)) := by omega
    rw [h1]; exact (hp m hm).2.2
end Good
end GlobalTheory.DetPowDegree
