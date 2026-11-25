-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.stable_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:54:39.499897+00:00
-- url     : https://prove2.me/submissions/cf055e29-d05d-482d-8334-149623118aca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi
namespace GlobalTheory.ZJ.SplitPull
theorem _root_.solution {V : G.left.Opens} (hV : Stable i V) : Stable i' (F ⁻¹ᵁ V) := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have := hV _ (pushPt hτ t) (pushPt hF.1.w g) h
  rwa [hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl] at this
end GlobalTheory.ZJ.SplitPull
