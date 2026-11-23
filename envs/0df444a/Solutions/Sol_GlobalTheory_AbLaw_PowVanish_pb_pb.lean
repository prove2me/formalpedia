-- Prove2me | solution 1 for GlobalTheory.AbLaw.PowVanish.pb_pb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:52.316047+00:00
-- url     : https://prove2.me/submissions/4007a35b-862b-4e9c-b217-2d2424b3fbba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent

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
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.PowVanish
theorem _root_.solution (g : Z ⟶ Y) (h : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (e' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)) :
    pb g e' (pb h e x) = pb (g ≫ h) (pre_comp g h e e') x :=
  congrArg (fun q => q.hom x) (Scheme.Hom.appLE_comp_appLE g h U V W e e')
end GlobalTheory.AbLaw.PowVanish
