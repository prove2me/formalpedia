-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.Pt.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:34.903562+00:00
-- url     : https://prove2.me/submissions/bf917faa-31e3-42fe-9c50-42ac973004b8

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
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
variable {N}
namespace GlobalTheory.GeneratorFunctor
namespace Pt
theorem _root_.solution {Z : Scheme.{0}} {x y : Pt N Z} (e : x = y) (k) (i) {T : Scheme.{0}} (a : T ⟶ Z)
    (W : T.Opens) (h h') : pb a _ W h (x.s k i) = pb a _ W h' (y.s k i) := by
  subst e; rfl
end Pt
end GlobalTheory.GeneratorFunctor
