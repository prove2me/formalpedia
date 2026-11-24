-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.isOpen_locTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:52:58.880026+00:00
-- url     : https://prove2.me/submissions/6638e80b-0551-4b52-8407-7aa9bd15d554

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution (p : Y ⟶ T) : IsOpen (locTriv L φ ε p) :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, hU, h⟩ => ⟨U, fun _ hy => ⟨U, hy, h⟩, U.isOpen, hU⟩
end GlobalTheory.AbLaw.CubeGen
