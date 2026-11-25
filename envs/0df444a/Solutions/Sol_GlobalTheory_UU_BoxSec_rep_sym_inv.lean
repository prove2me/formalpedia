-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.rep_sym_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:51.688456+00:00
-- url     : https://prove2.me/submissions/6114e1cf-6f28-4099-a23c-4544673df7d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_inv
import Theorems.Thm_GlobalTheory_UU_BoxSec_Rep_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UU.BoxSec
theorem _root_.solution (y : Y ⟶ D.P.A) :
    Rep D.P.L Y (fun _ _ h => (h (y⁻¹).left)⁻¹ * h y.left) (fun _ r z J => ((val D.sym (r ≫ y).left z J)⁻¹).val) :=
  (rep_inv D.sym D.sym_gen y.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show (h (y⁻¹).left ^ (1 : ℤ) * h (y.left ≫ 𝟙 _) ^ (-1 : ℤ))⁻¹ = _
      rw [Category.comp_id, zpow_one, zpow_neg_one, mul_inv, inv_inv])
    (fun _ _ _ _ _ => rfl)
end GlobalTheory.UU.BoxSec
