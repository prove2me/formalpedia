-- Prove2me | solution 1 for GlobalTheory.KunnethDomain.sec_ext_of_app_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:14.961505+00:00
-- url     : https://prove2.me/submissions/9fb69aa0-9372-4891-b338-67041f5660ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecOfGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqSumMulOfIsDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
noncomputable section
open GlobalTheory
open GlobalTheory.KunnethDomain
open ReciprocityTheory.ChartRestriction.G.DVR
variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.KunnethDomain
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ y J, Good L y J → sval u κ y J = sval t κ y J) : u = t :=
  SecOps.sec_ext fun j => by
    refine hκ (LB.wchart L φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ (h y I hI)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)
end GlobalTheory.KunnethDomain
