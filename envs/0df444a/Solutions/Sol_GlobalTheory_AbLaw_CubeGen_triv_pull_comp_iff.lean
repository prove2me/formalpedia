-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.triv_pull_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:07:57.997436+00:00
-- url     : https://prove2.me/submissions/a6e5cb00-e9fe-4312-bd78-5924e9910dc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_pull_iff

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
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution (q : W ⟶ Y) {Z : Scheme.{0}} (π : Z ⟶ W) :
    Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) ↔ TrivAt L φ ε (π ≫ q) := by
  rw [triv_pull_iff]
  unfold TrivAt
  simp only [Category.assoc]
end GlobalTheory.AbLaw.CubeGen
