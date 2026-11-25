-- Prove2me | solution 1 for GlobalTheory.GenericSection.polyImg_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:24:56.596573+00:00
-- url     : https://prove2.me/submissions/3452c627-0c2c-41a0-af31-39e01921f998

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
    (i : Fin (D + 1)) (k : Fin N) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0.succAbove k) = X (Sum.inr (i, k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]
end _root_.GlobalTheory.GenericSection
end GlobalTheory.GenericSection
