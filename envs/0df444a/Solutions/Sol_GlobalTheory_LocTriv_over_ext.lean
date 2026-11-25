-- Prove2me | solution 1 for GlobalTheory.LocTriv.over_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:52.841162+00:00
-- url     : https://prove2.me/submissions/97cd73df-28d3-4ac2-be5d-a351c254becd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
namespace GlobalTheory.LocTriv
theorem _root_.solution {Z Y : Over S} {a b : Z ⟶ Y} (h : ∀ z : Z.left, ∃ W, z ∈ W ∧ incl Z W ≫ a = incl Z W ≫ b) :
    a = b :=  by
  choose W hW he using h
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (Z.left.openCoverOfIsOpenCover W ?_) _ _ fun z => ?_
  · rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hW z⟩
  · have := congrArg (fun f => f.left) (he z)
    simp only [incl, Over.comp_left, Over.homMk_left] at this
    exact this
end GlobalTheory.LocTriv
