-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasisOfType.toMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:13:38.98601+00:00
-- url     : https://prove2.me/submissions/478381dd-914b-40f7-8c52-cdddb8232c0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left

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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (h : IsSymplecticBasisOfType B b d)
    (hB : B.IsAlt) : LinearMap.BilinForm.toMatrix b B =
      Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using IsSymplecticFamily.left_left h i j
  · simpa [Matrix.diagonal_apply] using IsSymplecticFamily.left_right h i j
  · have := IsSymplecticFamily.right_left h hB i j
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.diagonal_apply]
    rw [this]
    split_ifs <;> simp
  · simpa using IsSymplecticFamily.right_right h i j
end GlobalTheory.IsSymplecticBasisOfType
