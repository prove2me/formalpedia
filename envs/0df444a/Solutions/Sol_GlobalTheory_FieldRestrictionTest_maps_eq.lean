-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.maps_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:31.533683+00:00
-- url     : https://prove2.me/submissions/cf73e723-c72d-4282-b35d-8c8d5e7f1bae

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
theorem _root_.solution {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T} {g' : GtPtF D F}
    (H : GtPt.IsPullF F x g g') (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F g'.b χ k = x ≫ DegPre.gtφT D T g.b χ k := by
  have e := (GlobalTheory.TorusCoord.comp_eq_of_left g.b g'.b x (𝟙 _) (H.1.symm.trans (Category.id_comp _).symm)).1 χ k
  exact ((e.trans (Category.id_comp _)).trans (congrFun (GlobalTheory.TorusCoord.gtφT_eq g'.b χ) k).symm).symm
end GlobalTheory.FieldRestrictionTest
