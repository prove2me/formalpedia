-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.rep_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:43:03.258802+00:00
-- url     : https://prove2.me/submissions/9bc71407-750e-4faf-af57-e33ea97f267e

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


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
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UU.BoxSec
theorem _root_.solution {Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (q : Y.left ⟶ Y') :
    Rep L Y (fun _ _ h => ∏ k, h (q ≫ φ k) ^ ε k) (fun _ r z J => (val t (r.left ≫ q) z J).val) :=
  ⟨K, inferInstance, _, _, H1.SectionArithmetic.pullSec (genSec t ht) q, fun _ _ _ => rfl,
    fun _ _ z _ hJ => (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans (sval_genSec t ht _ z hJ)⟩
end GlobalTheory.UU.BoxSec
