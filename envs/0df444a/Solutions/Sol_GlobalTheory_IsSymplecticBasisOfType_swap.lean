-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:21.840723+00:00
-- url     : https://prove2.me/submissions/41edda4d-749b-4292-8aa9-c9925a3d8056

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_swap

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
theorem _root_.solution (h : IsSymplecticBasisOfType B b d) (hB : B.IsAlt) :
    IsSymplecticBasisOfType (-B) (b.reindex (Equiv.sumComm ι ι)) d := by
  simpa [IsSymplecticBasisOfType] using IsSymplecticFamily.swap h hB
end GlobalTheory.IsSymplecticBasisOfType
