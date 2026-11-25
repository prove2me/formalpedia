-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.rep_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:53:20.632878+00:00
-- url     : https://prove2.me/submissions/52e5f4f1-aab6-4dcc-ae14-e4f17f770623

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
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_sec
import Theorems.Thm_GlobalTheory_UU_BoxSec_Rep_congr
import Theorems.Thm_GlobalTheory_UU_BoxSec_prod_famT
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
theorem _root_.solution {T₀ : Over (Spec (CommRingCat.of R))} (ρ : Y ⟶ T₀) (x : Y ⟶ D.P.A) {α : D.X} {k : ℕ}
    (f : SecBT D T₀ k α) :
    Rep D.P.L Y (fun _ _ h => h x.left ^ ((k : ℤ) - 1) * h (x * cT D Y α).left * (h (cT D Y α).left)⁻¹ *
      h (1 : Y ⟶ D.P.A).left) (fun _ r z J => sval f (lift (r ≫ ρ) (r ≫ x)).left z J) :=
  (rep_sec f (lift ρ x).left).congr (fun _ _ h => prod_famT D ρ x α k h)
    (fun _ r z J _ => by rw [← Over.comp_left, comp_lift])
end GlobalTheory.UU.BoxSec
