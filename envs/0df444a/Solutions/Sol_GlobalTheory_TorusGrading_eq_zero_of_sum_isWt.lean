-- Prove2me | solution 1 for GlobalTheory.TorusGrading.eq_zero_of_sum_isWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:54.51864+00:00
-- url     : https://prove2.me/submissions/ae7465f9-fa5c-44d1-ac8b-5c61ecafb86a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_GlobalTheory_TorusGrading_eq_zero_of_sum_chV
import Theorems.Thm_GlobalTheory_TorusGrading_top_le_act
import Theorems.Thm_GlobalTheory_TorusGrading_exists_point
import Theorems.Thm_GlobalTheory_TorusGrading_val_comp
import Theorems.Thm_GlobalTheory_TorusGrading_top_le_comp_left
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
theorem _root_.solution (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {s : Finset X} {a : X → Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ) (hs : ∑ χ ∈ s, a χ = 0) {χ : X}
    (hχ : χ ∈ s) : a χ = 0 := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj (Eq.trans ?_ (map_zero _).symm)
  refine eq_zero_of_sum_chV Z₀ s (fun χ => (g₀.left.appLE V ⊤ h₀).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z₀ = p
  generalize snd (splitTorus S X) Z₀ = q
  have k := top_le_comp_left q h₀
  have := congrArg (((p ≫ i) * (q ≫ g₀)).left.appLE V ⊤ (top_le_act hst p k)).hom hs
  rw [map_sum, map_zero] at this
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) this
  rw [ha χ _ p (q ≫ g₀) _ k, ← chV_val, val_comp q h₀ k]
end GlobalTheory.TorusGrading
