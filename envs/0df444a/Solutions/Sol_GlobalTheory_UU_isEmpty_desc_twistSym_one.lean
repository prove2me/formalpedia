-- Prove2me | solution 1 for GlobalTheory.UU.isEmpty_desc_twistSym_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:35:48.87073+00:00
-- url     : https://prove2.me/submissions/f3f012a9-bfc3-4809-b9d4-e753f7df5655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
import Theorems.Thm_GlobalTheory_UU_TQ_Desc_exists_even
import Theorems.Thm_GlobalTheory_UU_not_exists_even_twistSym_one

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
theorem _root_.solution : IsEmpty ((TQ.torus (Spec (CommRingCat.of ℚ)) ℤ).Desc
    ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1)) := by
  constructor
  intro D
  exact not_exists_even_twistSym_one (TQ.Desc.exists_even D)
end GlobalTheory.UU
