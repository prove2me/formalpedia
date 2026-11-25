-- Prove2me | solution 1 for GlobalTheory.UU.BiTrivUniq.gen_eq_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:34.599491+00:00
-- url     : https://prove2.me/submissions/68465b88-37d2-4439-91d6-3af8f9156966

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTrivUniq
variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
namespace GlobalTheory.UU.BiTrivUniq
theorem _root_.solution (hM : M.IsLB) {t t' : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good M y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  refine unit_ext (V := LB.wchart M φ j) fun y hy => ?_
  obtain ⟨I, hI⟩ := exists_good_pt hM y
  exact (gen_trans ht (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans
    (gen_trans ht' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)
end GlobalTheory.UU.BiTrivUniq
