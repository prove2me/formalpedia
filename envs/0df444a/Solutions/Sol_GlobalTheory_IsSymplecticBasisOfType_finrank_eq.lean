-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:13:38.860496+00:00
-- url     : https://prove2.me/submissions/64ebe058-d62a-4861-8ce6-bf34abf44496

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}
open GlobalTheory.IsSymplecticBasisOfType
variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}
namespace GlobalTheory.IsSymplecticBasisOfType
theorem _root_.solution [Fintype ι] [StrongRankCondition R] (b : Basis (ι ⊕ ι) R M) :
    finrank R M = 2 * Fintype.card ι := by
  rw [finrank_eq_card_basis b, Fintype.card_sum, two_mul]
end GlobalTheory.IsSymplecticBasisOfType
