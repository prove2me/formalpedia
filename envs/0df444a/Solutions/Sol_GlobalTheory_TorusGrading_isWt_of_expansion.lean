-- Prove2me | solution 1 for GlobalTheory.TorusGrading.isWt_of_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:58:47.505022+00:00
-- url     : https://prove2.me/submissions/2d3f4018-f275-45cb-9f11-4465a0d3f737

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Theorems.Thm_GlobalTheory_TorusGrading_chV_comp
import Theorems.Thm_GlobalTheory_TorusGrading_eq_zero_of_sum_chV
import Theorems.Thm_GlobalTheory_TorusGrading_top_le_act
import Theorems.Thm_GlobalTheory_TorusGrading_val_comp
import Theorems.Thm_GlobalTheory_TorusGrading_val_congr
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
theorem _root_.solution [IsMonHom i]
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) {χ : X} (hχ : χ ∈ s) : IsWt i V (a χ) χ := by
  intro Z t g h₁ h₂
  rw [← chV_val, ← sub_eq_zero]
  refine eq_zero_of_sum_chV Z s (fun χ => (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (a χ) -
    (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z = p
  generalize snd (splitTorus S X) Z = q
  have k₁ := top_le_comp_left q h₁
  have k₂ := top_le_comp_left q h₂
  have e : (p ≫ i) * (q ≫ ((t ≫ i) * g)) = ((p * (q ≫ t)) ≫ i) * (q ≫ g) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, _root_.mul_assoc, Category.assoc]
  have a₁ := ha _ p _ (top_le_act hst p k₁) k₁
  have a₂ := ha _ (p * (q ≫ t)) _ (top_le_act hst _ k₂) k₂
  have a₃ := (a₁.symm.trans (val_congr e _ _ u)).trans a₂
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at a₃
  refine Eq.trans (Finset.sum_congr rfl fun ψ _ => ?_) a₃
  rw [val_comp q h₁ k₁, val_comp q h₂ k₂, chV_mul, Units.val_mul, chV_comp, map_sub, map_mul, mul_sub,
    _root_.mul_assoc]
end GlobalTheory.TorusGrading
