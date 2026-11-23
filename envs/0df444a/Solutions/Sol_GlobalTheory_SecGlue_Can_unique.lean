-- Prove2me | solution 1 for GlobalTheory.SecGlue.Can.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:34.685894+00:00
-- url     : https://prove2.me/submissions/3bb91dc2-b9ea-4f04-84e6-ef8af42df366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {B : Scheme.{0}} (G : Over B) {S T : Scheme.{0}}
variable {G}
namespace GlobalTheory.SecGlue
namespace Can
theorem _root_.solution {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} {pm pm'} (h : Can G f x x' pm)
    (h' : Can G f x x' pm') : pm = pm' :=
  pullback.hom_ext (f := x) (g := G.hom) (h.2.trans h'.2.symm) (h.1.trans h'.1.symm)
end Can
end GlobalTheory.SecGlue
