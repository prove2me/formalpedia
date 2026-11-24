-- Prove2me | solution 1 for GlobalTheory.SecGlue.exists_can
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:18.570749+00:00
-- url     : https://prove2.me/submissions/06cc5b78-68d7-4ec8-ae7b-576b4de27420

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
theorem _root_.solution {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} (e : f ≫ x = x') : ∃ pm, Can G f x x' pm :=
  ⟨((Over.homMk f e : Over.mk x' ⟶ Over.mk x) ▷ G).left,
    congrArg (·.left) (whiskerRight_snd (Over.homMk f e : Over.mk x' ⟶ Over.mk x) G),
    congrArg (·.left) (whiskerRight_fst (Over.homMk f e : Over.mk x' ⟶ Over.mk x) G)⟩
end GlobalTheory.SecGlue
