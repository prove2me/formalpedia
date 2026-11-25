-- Prove2me | solution 1 for GlobalTheory.TorusGrading.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:53.029794+00:00
-- url     : https://prove2.me/submissions/e6f86951-367e-4eca-9abb-8c15b95da3ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorusGrading
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
namespace GlobalTheory.TorusGrading
theorem _root_.solution (hV : IsAffineOpen V) : ∃ (Z : Over S) (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ V),
    Function.Injective (g.left.appLE V ⊤ h).hom := by
  refine ⟨Over.mk (hV.fromSpec ≫ G.hom), Over.homMk hV.fromSpec rfl, hV.fromSpec_preimage_self.ge, ?_⟩
  have h1 : hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  change Function.Injective (hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge).hom
  rw [h1]
  exact (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective
end GlobalTheory.TorusGrading
