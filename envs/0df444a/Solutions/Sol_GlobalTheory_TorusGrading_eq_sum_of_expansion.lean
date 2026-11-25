-- Prove2me | solution 1 for GlobalTheory.TorusGrading.eq_sum_of_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:06.393792+00:00
-- url     : https://prove2.me/submissions/6f8bcfbd-c956-40d8-8a8c-1c28e12c8e6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_GlobalTheory_TorusGrading_chV_one
import Theorems.Thm_GlobalTheory_TorusGrading_exists_point
import Theorems.Thm_GlobalTheory_TorusGrading_val_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution [IsMonHom i] (hV : IsAffineOpen V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) : u = ∑ χ ∈ s, a χ := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj ?_
  have e : ((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀ = g₀ := by rw [MonObj.one_comp, _root_.one_mul]
  have h₁ : ⊤ ≤ (((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀).left ⁻¹ᵁ V := by rw [e]; exact h₀
  rw [map_sum, ← val_congr e h₁ h₀ u, ha Z₀ 1 g₀ h₁ h₀]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [chV_one, Units.val_one, _root_.one_mul]
end GlobalTheory.TorusGrading
