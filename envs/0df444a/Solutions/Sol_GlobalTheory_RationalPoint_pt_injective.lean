-- Prove2me | solution 1 for GlobalTheory.RationalPoint.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:52.727034+00:00
-- url     : https://prove2.me/submissions/ef93a84a-68af-4181-a4e4-ef61208457ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup

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
open Topology
open GlobalTheory
open GlobalTheory.RationalPoint
variable {k : Type} [Field k]
variable [IsAlgClosed k]
namespace GlobalTheory.RationalPoint
theorem _root_.solution {X : Over (Sp k)} [LocallyOfFiniteType X.hom] :
    Function.Injective (pt : (𝟙_ (Over (Sp k)) ⟶ X) → X.left) := fun x y h =>
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y) h)
end GlobalTheory.RationalPoint
