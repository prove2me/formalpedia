-- Prove2me | solution 1 for GlobalTheory.SecGlue.glue_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:13.993201+00:00
-- url     : https://prove2.me/submissions/a0a6c3f1-f5b7-4128-96bd-69dcd4f7fb29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
import Theorems.Thm_GlobalTheory_SecGlue_gs_appLE
import Theorems.Thm_GlobalTheory_SecGlue_gs_inj
import Theorems.Thm_GlobalTheory_SecGlue_exists_appLE_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {X Y Z : Scheme.{0}}
variable {J : Type} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
namespace GlobalTheory.SecGlue
theorem _root_.solution (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) (W : ∀ i, (T i).Opens)
    (hW : ∀ i y, y ∈ W i ↔ a i y ∈ V) (u : ∀ i, Γ(T i, W i))
    (h : ∀ i j y y', a i y = a j y' → y ∈ W i → ∃ (Z : Scheme.{0}) (b : Z ⟶ T i) (c : Z ⟶ T j) (z : Z),
      IsOpenImmersion (b ≫ a i) ∧ b ≫ a i = c ≫ a j ∧ b z = y ∧ gs b z _ (u i) = gs c z _ (u j)) :
    ∃ s : Γ(X, V), ∀ i y, y ∈ W i → gs (a i) y V s = gs (𝟙 _) y _ (u i) := by
  have e : ∀ i, W i = a i ⁻¹ᵁ (V ⊓ (a i).opensRange) := fun i => by
    ext y
    exact ⟨fun h => ⟨(hW i y).1 h, y, rfl⟩, fun h => (hW i y).2 h.1⟩
  choose w hw using fun i => exists_appLE_eq (a i) inf_le_right (e i) (u i)
  have v : ∀ i (Z : Scheme.{0}) (r : Z ⟶ T i) (z : Z), r z ∈ W i →
      gs r z _ (u i) = gs (r ≫ a i) z _ (w i) := fun i Z r z hz => by
    rw [← hw i, gs_appLE r (a i) z _ _ _ hz]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V ⊓ (a i).opensRange) V
    (fun i => homOfLE inf_le_left) (fun x hx => by
      obtain ⟨i, y, rfl⟩ := hc x
      exact Opens.mem_iSup.2 ⟨i, hx, y, rfl⟩) w
    (fun k l => fn_ext (V := (V ⊓ (a k).opensRange) ⊓ (V ⊓ (a l).opensRange)) fun x hx => by
      refine (gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_
        (gs_res (𝟙 X) x inf_le_right hx _).symm)
      obtain ⟨y, rfl⟩ := hx.1.2
      obtain ⟨y', hy'⟩ := hx.2.2
      obtain ⟨Z, b, c, z, _, e1, rfl, e2⟩ := h k l y y' hy'.symm ((hW k y).2 hx.1.1)
      have hcz : c z ∈ W l := by
        rw [hW, ← Scheme.Hom.comp_apply, ← e1]; exact hx.1.1
      rw [v k Z b z ((hW k _).2 hx.1.1), v l Z c z hcz, ← e1] at e2
      exact gs_inj (b ≫ a k) z hx.1 hx.2 e2)
  refine ⟨s, fun i y hy => ?_⟩
  rw [v i _ (𝟙 _) y hy, Category.id_comp, ← hs i]
  exact (gs_res (a i) y inf_le_left ((e i).le hy) s).symm
end GlobalTheory.SecGlue
