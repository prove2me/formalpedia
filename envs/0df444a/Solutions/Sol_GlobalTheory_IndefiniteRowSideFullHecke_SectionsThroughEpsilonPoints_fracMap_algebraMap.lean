-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:04.872473+00:00
-- url     : https://prove2.me/submissions/5657db42-3940-410f-a86d-ebc2e63718e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_ArcFramePointTruncation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (dualMap FrPt Gx PPx IsCombAt embK)
open scoped CategoryTheory.Obj
variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {g : A →+* A'}
  {D₀ : Out.DegPre A} {D₁ : Out.DegPre A'}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
theorem _root_.solution (hg : Function.Injective g) (r : A) :
    fracMap g hg (algebraMap A _ r) = algebraMap A' _ (g r) := IsFractionRing.lift_algebraMap _ r
end GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
