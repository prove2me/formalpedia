-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.isPullF_iff_isPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:25.676688+00:00
-- url     : https://prove2.me/submissions/ab2921a6-ae80-4329-a18d-afb9623c13f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution (x : Spec (CommRingCat.of F) ⟶ T.left) (g : GtPt D T) (g' : GtPtF D F) :
    GtPt.IsPullF F x g g' ↔ GtPt.IsPull (T' := TF (R := R) F) x g (toT g') := Iff.rfl
end GlobalTheory.FieldRestrictionTest
