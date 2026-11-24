-- Prove2me | solution 1 for GlobalTheory.SecGlue.gs_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:23.177349+00:00
-- url     : https://prove2.me/submissions/9726a40b-2441-4022-a28e-7958e7db9651

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
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.SecGlue
theorem _root_.solution (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 X) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h _).symm
end GlobalTheory.SecGlue
