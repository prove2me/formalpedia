-- Prove2me | solution 1 for GlobalTheory.KunnethDomain.sval_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:29.891425+00:00
-- url     : https://prove2.me/submissions/a1f93c26-27a0-49c0-af2b-a6912d42185c

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : T ⟶ Y') (z : T) {J} (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
    (wchart_comp_le φ h _ hm) _)
end GlobalTheory.KunnethDomain
