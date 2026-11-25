-- Prove2me | solution 1 for GlobalTheory.app_sec_eq_zero_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:22.578015+00:00
-- url     : https://prove2.me/submissions/14f0c56e-de46-400e-8026-a8d2c28a03ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j) : (r.app _).hom (d.f j) = 0 := by
  apply TopCat.Presheaf.section_ext Z.sheaf _
  intro z hz
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := sec_trans d r z (j := j) hz (Good.mem hI φ r)
  have e' : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    e.trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  exact ((gs_eq r z _ hz _).symm.trans e').trans (map_zero _).symm
end GlobalTheory
