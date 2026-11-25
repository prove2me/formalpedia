-- Prove2me | solution 1 for GlobalTheory.CompletePoint.corr_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:34:33.040632+00:00
-- url     : https://prove2.me/submissions/9e4dfd0c-a2e0-45aa-bd73-7642a3dff4d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_fn_eq_of_thick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] (I : Ideal R) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}
namespace GlobalTheory.CompletePoint
theorem _root_.solution [IsHausdorff I R] (hL : L.IsLB) (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)}
    (hu : u.IsGen) {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z J, Good L z J → val u (thick R I e) z J = val u' (thick R I e) z J) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL h u hu u' hu'
  have h1 : ∀ e, pullU (thick R I e) ⊤ a = 1 := fun e => unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL z
    have := ha _ (thick R I e) z J hJ
    rw [hv e z J hJ] at this
    rw [gm_pull (𝟙 _) (thick R I e) z ⊤ trivial, Category.id_comp, map_one]
    exact (mul_eq_right.1 this.symm)
  have h2 : a = 1 := Units.ext (fn_eq_of_thick I fun e =>
    (congrArg Units.val (h1 e)).trans (map_one _).symm)
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]
end GlobalTheory.CompletePoint
