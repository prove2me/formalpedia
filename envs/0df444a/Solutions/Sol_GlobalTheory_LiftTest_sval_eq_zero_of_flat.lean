-- Prove2me | solution 1 for GlobalTheory.LiftTest.sval_eq_zero_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:47.394841+00:00
-- url     : https://prove2.me/submissions/0ad77872-c010-43a8-af8e-0f16cba72c61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_GlobalTheory_LiftTest_stalkMap_injective_of_flat
import Theorems.Thm_GlobalTheory_LiftTest_gs_comp
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
open GlobalTheory GlobalTheory.LiftTest
namespace GlobalTheory.LiftTest
theorem _root_.solution {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (f : W ⟶ Z) [Flat f] (w : W)
    (h : ∀ J, Good L w J → sval d (f ≫ r) w J = 0) (J) (hJ : Good L (f w) J) : sval d r (f w) J = 0 := by
  choose I hI using fun χ : W ⟶ X => exists_chart hL (χ w)
  have hm : r (f w) ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have e := sec_trans d (f ≫ r) w (j := fun k => J (r ≫ φ k)) hm (Good.mem hI φ (f ≫ r))
  have e0 : gs (f ≫ r) w (LB.wchart L φ (fun k => I ((f ≫ r) ≫ φ k))) (d.f (fun k => I ((f ≫ r) ≫ φ k))) = 0 := h I hI
  rw [e0, mul_zero] at e
  exact (map_eq_zero_iff _ (stalkMap_injective_of_flat f w)).1 ((gs_comp f r w _ hm _).symm.trans e)
end GlobalTheory.LiftTest
