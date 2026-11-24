-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.cover_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:53.513848+00:00
-- url     : https://prove2.me/submissions/e334d5eb-1948-4cc8-8170-9e3cce1233ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections

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
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GeneratorFunctor
theorem _root_.solution {Y : Scheme.{0}} (𝒰 : Y.OpenCover) (V : Y.Opens) (x y : Γ(Y, V)ˣ)
    (h : ∀ i, pb (𝒰.f i) V _ le_rfl x = pb (𝒰.f i) V _ le_rfl y) : x = y := by
  ext
  refine 𝒰.ext_elem _ _ fun i => ?_
  have := congrArg Units.val (h i)
  rwa [pb_val, pb_val, ← Scheme.Hom.app_eq_appLE] at this
end GlobalTheory.GeneratorFunctor
