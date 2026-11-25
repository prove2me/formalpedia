-- Prove2me | solution 1 for GlobalTheory.UU.torus_stable_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:39.349041+00:00
-- url     : https://prove2.me/submissions/d2059521-d2db-46ec-a42b-378fcbc29564

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Theorems.Thm_GlobalTheory_UU_torus_stable_of_surjective
import Theorems.Thm_GlobalTheory_UU_surjective_red


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
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G), TorusCompat (red J) F i₀ i → ∀ W : G.left.Opens, (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤ ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) → (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  intro A _ J hJ X _ G _ G₀ _ F hF i₀ i hi W hW
  haveI := surjective_red hJ
  exact torus_stable_of_surjective (red J) X G G₀ F hF i₀ i hi W hW
end GlobalTheory.UU
