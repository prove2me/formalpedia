-- Prove2me | solution 1 for GlobalTheory.SpecialFibreGenerator.mem_nonzeroLocus_secAlong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:10:07.174807+00:00
-- url     : https://prove2.me/submissions/22cdeb1e-4a57-4734-b75c-815cc0a539f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre

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
open GlobalTheory
open GlobalTheory.SpecialFibreGenerator
open TopologicalSpace Opposite
variable {X Y : Scheme.{0}}
namespace GlobalTheory.SpecialFibreGenerator
theorem _root_.solution {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  rw [Scheme.basicOpen_appLE]
  exact ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩
end GlobalTheory.SpecialFibreGenerator
