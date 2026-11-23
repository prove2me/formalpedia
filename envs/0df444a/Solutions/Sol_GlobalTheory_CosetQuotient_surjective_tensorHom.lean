-- Prove2me | solution 1 for GlobalTheory.CosetQuotient.surjective_tensorHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:15.531852+00:00
-- url     : https://prove2.me/submissions/668f39b2-7729-46bd-aacf-54078873d6ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.CosetQuotient
universe v u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.CosetQuotient
theorem _root_.solution {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  have hc : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective :=
    ⟨fun _ _ hf hg => by
      have := hf
      have := hg
      infer_instance⟩
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Surjective) hf hg (Over.w f).symm
    (Over.w g).symm
end GlobalTheory.CosetQuotient
