-- Prove2me | solution 1 for GlobalTheory.PsiSpread.exists_gen_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:36.269428+00:00
-- url     : https://prove2.me/submissions/2dedbcf1-5073-41d8-81f6-269c4ae6fce6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
noncomputable section
open GlobalTheory
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.PsiSpread
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j : K → L.ι) (hj : ∀ y, y ∈ LB.wchart L φ j) (V : Y.Opens) (hV : ∀ y, y ∈ V) (u : Γ(Y, V)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u := by
  let t : LB.Gen (LB.LinComb L φ ε) := ⟨fun j' =>
    res (le_inf le_rfl (fun y _ => hj y) : LB.wchart L φ j' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j' j) * res (fun y _ => hV y : LB.wchart L φ j' ≤ V) u⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u :=
    fun Z r z j' h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ h _).trans (gm_linComb L φ ε r z j' j h (hj _))) (gm_res r z _ h _))
  refine ⟨t, fun (i i' : K → L.ι) => unit_ext fun y hy => ?_, key⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y i i' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i' hy.2))).trans ?_)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hj _), _root_.mul_assoc]
  rfl
end GlobalTheory.PsiSpread
