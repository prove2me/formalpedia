-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.trivAt_of_formal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:01.783682+00:00
-- url     : https://prove2.me/submissions/218a7b50-47bf-4eb1-8ea7-c6ab8838d4f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
theorem _root_.solution {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (r : Z ⟶ Y)
    (h : ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U), ∏ i, k (r ≫ φ i) ^ ε i = 1) : TrivAt L φ ε r := by
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := fun i => r ≫ φ i) (ε' := ε)
    (fun U _ k => (Fintype.prod_empty _).trans (h U k).symm) (LB.oneGen L (Y := Z))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact ⟨t, ht⟩
end GlobalTheory.AbLaw.CubeGen
