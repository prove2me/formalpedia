-- Prove2me | solution 1 for GlobalTheory.GenericSection.polyImg_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:26:16.319695+00:00
-- url     : https://prove2.me/submissions/9aa0f5fc-f719-4d01-8708-a990d35f758c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
open GlobalTheory GlobalTheory.GenericSection
variable {F : Type} [Field F] {D N : ℕ}
open NumberField MvPolynomial
variable {F : Type} [Field F] {D N : ℕ}
namespace GlobalTheory.GenericSection
namespace _root_.GlobalTheory.GenericSection
theorem _root_.solution (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0) =
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]
end _root_.GlobalTheory.GenericSection
end GlobalTheory.GenericSection
