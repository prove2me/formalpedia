-- Prove2me | solution 1 for GlobalTheory.Published.AbMulNSt.finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:33.904907+00:00
-- url     : https://prove2.me/submissions/e61e0143-d274-4205-af86-03a1309bca18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.AbMulNSt
variable {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] {g n : ℕ}
namespace GlobalTheory.Published.AbMulNSt
theorem _root_.solution (h : AbMulNSt) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom)
    (hn : (n : k) ≠ 0) : Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [h k B g n hB hg hn]
  refine pow_ne_zero _ ?_
  rintro rfl
  exact hn Nat.cast_zero
end GlobalTheory.Published.AbMulNSt
