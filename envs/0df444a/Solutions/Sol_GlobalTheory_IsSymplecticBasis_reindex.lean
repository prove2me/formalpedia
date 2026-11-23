-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:28.962188+00:00
-- url     : https://prove2.me/submissions/4f177f56-7d54-4c37-b7a0-68855c4869c9

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
open GlobalTheory.IsSymplecticBasis
variable {b : Basis (ι ⊕ ι) R M}
namespace GlobalTheory.IsSymplecticBasis
theorem _root_.solution {κ : Type*} (h : IsSymplecticBasis B b) (σ : ι ≃ κ) :
    IsSymplecticBasis B (b.reindex (σ.sumCongr σ)) :=
  IsSymplecticBasisOfType.reindex h σ
end GlobalTheory.IsSymplecticBasis
