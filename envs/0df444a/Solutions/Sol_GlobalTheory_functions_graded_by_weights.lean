-- Prove2me | solution 1 for GlobalTheory.functions_graded_by_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:19:29.364313+00:00
-- url     : https://prove2.me/submissions/bea34de1-7ba4-4588-92a1-ca557fbda41b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_GlobalTheory_TorusGrading_exists_expansion
import Theorems.Thm_GlobalTheory_TorusGrading_isWt_of_expansion
import Theorems.Thm_GlobalTheory_TorusGrading_eq_zero_of_sum_isWt
import Theorems.Thm_GlobalTheory_TorusGrading_eq_sum_of_expansion
import Theorems.Thm_GlobalTheory_UU_isWt_zero


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
open TorusGrading
namespace GlobalTheory
theorem _root_.solution :
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by
  intro S G _ X _ i hi V hV hst
  refine ⟨fun u => ?_, fun a ha hs => ?_⟩
  · obtain ⟨a, ha⟩ := exists_expansion hV hst u
    refine ⟨a, fun χ => ?_, eq_sum_of_expansion hV ha⟩
    by_cases hχ : χ ∈ a.support
    · exact isWt_of_expansion hst ha hχ
    · rw [Finsupp.notMem_support_iff.1 hχ]
      exact isWt_zero χ
  · refine Finsupp.ext fun χ => ?_
    by_contra h
    exact h (eq_zero_of_sum_isWt hV hst ha hs (Finsupp.mem_support_iff.2 h))
end GlobalTheory
