-- Prove2me | solution 1 for GlobalTheory.SecLift.stalkMap_gr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:39.080523+00:00
-- url     : https://prove2.me/submissions/b35fa3cb-0104-46e7-907a-3831d0eaaf9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution (j : Y ⟶ X) (y : Y) (U : X.Opens) (h : j y ∈ U) (s : Γ(X, U)) :
    (j.stalkMap y).hom (gr (𝟙 X) (j y) U h s) = gr (𝟙 Y ≫ j) y U h s :=
  j.germ_stalkMap_apply U y h s
end GlobalTheory.SecLift
