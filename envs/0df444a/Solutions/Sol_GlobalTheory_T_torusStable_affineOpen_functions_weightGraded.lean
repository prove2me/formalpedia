-- Prove2me | solution 1 for GlobalTheory.T.torusStable_affineOpen_functions_weightGraded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:01:03.291906+00:00
-- url     : https://prove2.me/submissions/57394aca-169e-49d3-9b76-5dab81c60853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Theorems.Thm_GlobalTheory_functions_graded_by_weights


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by
  first | exact @GlobalTheory.functions_graded_by_weights | exact GlobalTheory.functions_graded_by_weights | (intros; apply GlobalTheory.functions_graded_by_weights <;> assumption)
end _root_.GlobalTheory.T
