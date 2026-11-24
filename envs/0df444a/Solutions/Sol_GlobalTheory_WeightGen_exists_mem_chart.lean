-- Prove2me | solution 1 for GlobalTheory.WeightGen.exists_mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:57.497482+00:00
-- url     : https://prove2.me/submissions/ebf7eeea-16b9-4a0d-b5be-fec9507308f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {S : Scheme.{0}}
variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)
attribute [local instance] SplitExt.free SplitExt.finite
namespace GlobalTheory.WeightGen
theorem _root_.solution (x : E.B.left) : ∃ j, x ∈ E.chart j := by
  choose j hj using fun k => exists_chart (E.O (E.basis k)).isLB x
  refine ⟨j, ?_⟩
  have : ((E.chart j : E.B.left.Opens) : Set E.B.left) =
      ⋂ k, ((E.O (E.basis k)).L.U (j k) : Set E.B.left) := TopologicalSpace.Opens.coe_iInf _
  exact this.ge (Set.mem_iInter.2 hj)
end GlobalTheory.WeightGen
