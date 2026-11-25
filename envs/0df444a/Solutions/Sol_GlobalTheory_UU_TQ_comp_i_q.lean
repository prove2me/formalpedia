-- Prove2me | solution 1 for GlobalTheory.UU.TQ.comp_i_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:21:20.115246+00:00
-- url     : https://prove2.me/submissions/ca5899aa-0ecd-4414-a601-22d74cac2af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
namespace TQ
theorem _root_.solution (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) : (t ≫ Q.i) ≫ Q.q = 1 := by
  rw [Category.assoc, Q.isKernel.w, ← Category.assoc]
  simp only [toUnit_unique (t ≫ toUnit _) (toUnit T)]
  rfl
end TQ
end GlobalTheory.UU
