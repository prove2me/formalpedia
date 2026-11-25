-- Prove2me | solution 1 for GlobalTheory.isTangent_comp_of_isMonHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:54.378743+00:00
-- url     : https://prove2.me/submissions/a18c9f14-fc7c-4436-880a-1fa063e2736b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {B G : Over (Sp R)} [GrpObj B] [GrpObj G]
    (Φ : B ⟶ G) [IsMonHom Φ] (v : epsR R ⟶ B) (hv : IsTangent v) : IsTangent (v ≫ Φ) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
end GlobalTheory
