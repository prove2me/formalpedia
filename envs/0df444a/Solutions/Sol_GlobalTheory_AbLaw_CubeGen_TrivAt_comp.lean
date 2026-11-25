-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.TrivAt.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:27.346901+00:00
-- url     : https://prove2.me/submissions/620af7a3-6ea8-4cc4-a065-4c213b76b04f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y Z Z' T : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.AbLaw.CubeGen
namespace TrivAt
theorem _root_.solution {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {r : Z ⟶ Y} (H : TrivAt L φ ε r)
    (h : Z' ⟶ Z) : TrivAt L φ ε (h ≫ r) := by
  obtain ⟨t, ht⟩ := H
  have e : (fun k => (h ≫ r) ≫ φ k) = fun k => h ≫ r ≫ φ k := funext fun k => Category.assoc _ _ _
  unfold TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ t ht h⟩
end TrivAt
end GlobalTheory.AbLaw.CubeGen
