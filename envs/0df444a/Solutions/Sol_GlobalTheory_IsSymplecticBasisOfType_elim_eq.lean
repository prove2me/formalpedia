-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.elim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:35.970801+00:00
-- url     : https://prove2.me/submissions/5ee51422-decc-47e5-b37d-cb08fb1fdfbc

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
theorem _root_.solution (b : Basis (ι ⊕ ι) R M) :
    Sum.elim (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) = b := by
  funext i; cases i <;> rfl
end GlobalTheory.IsSymplecticBasisOfType
