-- Prove2me | solution 1 for GlobalTheory.isSemiAbelian_of_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:52.554627+00:00
-- url     : https://prove2.me/submissions/7f845d41-c4b0-4815-839e-f98c02eef13a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt
import Theorems.Thm_GlobalTheory_nonempty_torusExtension_of_isGt
import Theorems.Thm_GlobalTheory_GtBaseChange_isGt_extBC
import Theorems.Thm_GlobalTheory_UnitRigidity_smooth_geometricallyConnected_of_isGt


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
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G],
    E.IsGt G → IsSemiAbelian G := by
  intro S E G _ hc h
  obtain ⟨hs, hg⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  obtain ⟨d⟩ := h
  have := d.q_affine
  have := E.isAbelian.proper
  refine ⟨hc, hs, ?_, ?_, hg, fun Ω _ _ p => ?_⟩
  · rw [← Over.w d.q]
    infer_instance
  · rw [← Over.w d.q]
    infer_instance
  · exact nonempty_torusExtension_of_isGt _ _ (GtBaseChange.isGt_extBC p E G d)
end GlobalTheory
