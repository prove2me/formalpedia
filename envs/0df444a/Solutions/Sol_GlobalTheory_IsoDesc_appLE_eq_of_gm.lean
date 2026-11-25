-- Prove2me | solution 1 for GlobalTheory.IsoDesc.appLE_eq_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:06:36.325702+00:00
-- url     : https://prove2.me/submissions/01b14deb-b767-4316-95ac-fc563238501e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_appTop_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.IsoDesc
theorem _root_.solution (r r' : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (h' : ⊤ ≤ r' ⁻¹ᵁ U) (a : Γ(Y, U)ˣ)
    (e : ∀ z, gm r z U a = gm r' z U a) : (r.appLE U ⊤ h).hom a.val = (r'.appLE U ⊤ h').hom a.val := by
  have k : ∀ (r : Z ⟶ Y) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z), gm (𝟙 Z) z ⊤ (res h (pullU r U a)) = gm r z U a := fun r h z => by
    rw [gm_res (𝟙 Z) z h trivial, gm_pull (𝟙 Z) r z U (h trivial), Category.id_comp]
  exact (appTop_eq_iff (res h (pullU r U a)) (res h' (pullU r' U a))).2 fun z => by rw [k, k, e]
end GlobalTheory.IsoDesc
