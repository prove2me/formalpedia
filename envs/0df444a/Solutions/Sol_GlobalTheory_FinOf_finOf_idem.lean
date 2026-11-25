-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:47:00.471334+00:00
-- url     : https://prove2.me/submissions/bf6a42a9-7179-4cd5-a583-4f737748317d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
namespace GlobalTheory.FinOf
theorem _root_.solution {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
  · right
    exact hu.mul_left_cancel (by rw [_root_.mul_one]; exact h.eq)
  · left
    exact hu.mul_left_cancel (by rw [mul_zero]; exact h.one_sub_mul_self)
end GlobalTheory.FinOf
