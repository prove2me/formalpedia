-- Prove2me | solution 1 for GlobalTheory.Exist.CubicalExtension.exists_quot_of_isos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:46:59.878665+00:00
-- url     : https://prove2.me/submissions/f735da52-c2e3-49ca-bffe-d4c9f33e816f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
import Theorems.Thm_GlobalTheory_Exist_CubicalExtension_mem_qchart
import Theorems.Thm_GlobalTheory_Exist_CubicalExtension_isGen_quot
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.CubicalExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' X'' A : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
namespace GlobalTheory.Exist.CubicalExtension
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (w' : LB.Iso L'' (L'.pull F'))
    (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw' : PGen w') (hw'' : PGen w'') (κ : A ⟶ X'') (j : A ⟶ X')
    (hj : κ ≫ F' = j) :
    ∃ r : LB.Gen ((LB.div (L.pull F) L').pull j), r.IsGen ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) a i k, F (j (f y)) ∈ L.U a → j (f y) ∈ L'.U i → κ (f y) ∈ L''.U k →
        gm f y (qchart L L' F j a i) (r.s (fun _ => (fun _ => a, i))) =
          gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ := by
  subst hj
  have glue : ∀ a i, ∃ s : Γ(A, qchart L L' F (κ ≫ F') a i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) k,
      F (F' (κ (f y))) ∈ L.U a → F' (κ (f y)) ∈ L'.U i → κ (f y) ∈ L''.U k →
        gm f y _ s = gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ := by
    intro a i
    obtain ⟨W, hW⟩ : ∃ W : L''.ι → A.Opens, ∀ k x, x ∈ W k ↔
        F (F' (κ x)) ∈ L.U a ∧ F' (κ x) ∈ L'.U i ∧ κ x ∈ L''.U k :=
      ⟨fun k => κ ⁻¹ᵁ (F' ⁻¹ᵁ (F ⁻¹ᵁ L.U a) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k)), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ k, W k ≤ qchart L L' F (κ ≫ F') a i := fun k x hx =>
      mem_qchart.2 ⟨((hW k x).1 hx).1, ((hW k x).1 hx).2.1⟩
    have l₁ : ∀ k, W k ≤ κ ⁻¹ᵁ ((L.pull (F' ≫ F)).U (fun _ => a) ⊓ L''.U k) := fun k x hx =>
      ⟨mem_pull₂.2 ((hW k x).1 hx).1, ((hW k x).1 hx).2.2⟩
    have l₂ : ∀ k, W k ≤ κ ⁻¹ᵁ ((L'.pull F').U (fun _ => i) ⊓ L''.U k) := fun k x hx =>
      ⟨mem_pull.2 ((hW k x).1 hx).2.1, ((hW k x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(A, W k)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) k, f y ∈ W k →
        gm f y (W k) (u k) = gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ :=
      ⟨fun k => res (l₁ k) (pullU κ _ (w''.s (fun _ => a, k))) * (res (l₂ k) (pullU κ _ (w'.s (fun _ => i, k))))⁻¹,
        fun Y f y k hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ k) hy _).trans (gm_pull f κ y _ (l₁ k hy) _))
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f y (l₂ k) hy _).trans (gm_pull f κ y _ (l₂ k hy) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hL'' (κ x)
        exact Opens.mem_iSup.2 ⟨k, (hW k x).2 ⟨(mem_qchart.1 hx).1, (mem_qchart.1 hx).2, hk⟩⟩) u (fun k k' x hx => by
        have h₁ := (hW k x).1 hx.1
        have h₂ := (hW k' x).1 hx.2
        have e₁ := hw'' _ (𝟙 A ≫ κ) x a a k k' h₁.1 h₁.1 h₁.2.2 h₂.2.2
        have e₂ := hw' _ (𝟙 A ≫ κ) x i i k k' h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hL _ x h₁.1] at e₁
        rw [gm_self hL' _ x h₁.2.1] at e₂
        rw [hu _ (𝟙 A) x k hx.1, hu _ (𝟙 A) x k' hx.2, e₁, e₂]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Y f y k h₁ h₂ h₃ => ?_⟩
    have hy := (hW k (f y)).2 ⟨h₁, h₂, h₃⟩
    exact (gm_res f y (l₀ k) hy s).symm.trans ((congrArg (gm f y (W k)) (hs k)).trans (hu Y f y k hy))
  choose s hs using glue
  refine ⟨_, isGen_quot s fun y a a' i i' ha ha' hi hi' => ?_, fun Y f y a i k => hs a i Y f y k⟩
  obtain ⟨k, hk⟩ := exists_chart hL'' (κ y)
  have e₁ := hw'' _ (𝟙 A ≫ κ) y a a' k k ha ha' hk hk
  have e₂ := hw' _ (𝟙 A ≫ κ) y i i' k k hi hi' hk hk
  rw [hs a i _ (𝟙 A) y k ha hi hk, hs a' i' _ (𝟙 A) y k ha' hi' hk, e₁, e₂, Category.id_comp, Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.Exist.CubicalExtension
