-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.toMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:48.340664+00:00
-- url     : https://prove2.me/submissions/a0412c86-b6b9-41f3-b73d-dcd7ff736698

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_toMatrix_eq

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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) :
    LinearMap.BilinForm.toMatrix b B = -Matrix.J ι R := by
  rw [IsSymplecticBasisOfType.toMatrix_eq h hB, Matrix.J, Matrix.fromBlocks_neg]
  simp
end GlobalTheory.IsSymplecticBasis
