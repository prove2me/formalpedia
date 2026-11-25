-- Prove2me | solution 1 for GlobalTheory.unit_eq_one_of_axes_of_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:04.027829+00:00
-- url     : https://prove2.me/submissions/96a87854-36d5-475b-822f-a3b068468eb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_UnitRigidity_smooth_geometricallyConnected_of_isGt
import Theorems.Thm_GlobalTheory_UnitRigidity_unit_eq_one_of_axes
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open UnitRigidity
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ u : Γ((G ⊗ G).left, ⊤), IsUnit u → (lift (𝟙 G) (1 : G ⟶ G)).left.appTop.hom u = 1 → (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom u = 1 → u = 1 := by
  intro K _ _ E G _ h u hu u₁ u₂
  obtain ⟨_, _⟩ := smooth_geometricallyConnected_of_isGt E G h
  have := geometricallyIntegral_of_smooth G.hom
  have h1 : (1 : G ⟶ G).left = G.hom ≫ (η[G] : 𝟙_ _ ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  refine unit_eq_one_of_axes G.hom (η[G] : 𝟙_ _ ⟶ G).left (Over.w _) _ _ ?_ ?_ ?_ ?_ u hu u₁ u₂
  · exact congrArg (·.left) (lift_fst (𝟙 G) (1 : G ⟶ G))
  · exact (congrArg (·.left) (lift_snd (𝟙 G) (1 : G ⟶ G))).trans h1
  · exact (congrArg (·.left) (lift_fst (1 : G ⟶ G) (𝟙 G))).trans h1
  · exact congrArg (·.left) (lift_snd (1 : G ⟶ G) (𝟙 G))
end GlobalTheory
