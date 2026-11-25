-- Prove2me | solution 1 for GlobalTheory.GenScheme.pb_pb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:17.111406+00:00
-- url     : https://prove2.me/submissions/be75375d-96b8-49a7-a349-f936aa6fd8a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenScheme
theorem _root_.solution (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h a) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) a :=
  Units.ext (congr($(Scheme.Hom.appLE_comp_appLE g f U V W h h').hom a.val))
end GlobalTheory.GenScheme
