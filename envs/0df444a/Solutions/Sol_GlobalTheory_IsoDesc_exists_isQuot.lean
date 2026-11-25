-- Prove2me | solution 1 for GlobalTheory.IsoDesc.exists_isQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:11.910937+00:00
-- url     : https://prove2.me/submissions/b9c7216c-cea4-4c7b-a83c-707458d8f306

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}
namespace GlobalTheory.IsoDesc
theorem _root_.solution (hL : L.IsLB) (hM' : M'.IsLB) (hM : M.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) : ∃ s, IsQuot u w s := by
  have glue : ∀ (j : M.ι) (i : M'.ι), ∃ s : Γ(G, q ⁻¹ᵁ dom M' M β j i)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) (k : L.ι), β (q (f y)) ∈ M.U j → q (f y) ∈ M'.U i → f y ∈ L.U k →
        gm f y _ s = gw w f y j k * (gw u f y i k)⁻¹ := by
    intro j i
    obtain ⟨W, hW⟩ : ∃ W : L.ι → G.Opens, ∀ k x, x ∈ W k ↔ β (q x) ∈ M.U j ∧ q x ∈ M'.U i ∧ x ∈ L.U k :=
      ⟨fun k => q ⁻¹ᵁ (β ⁻¹ᵁ M.U j) ⊓ (q ⁻¹ᵁ M'.U i ⊓ L.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ k, W k ≤ q ⁻¹ᵁ dom M' M β j i := fun k x hx =>
      ⟨mem_pull.2 ((hW k x).1 hx).1, ((hW k x).1 hx).2.1⟩
    have l₁ : ∀ k, W k ≤ (M.pull (q ≫ β)).U (fun _ => j) ⊓ L.U k := fun k x hx =>
      ⟨mem_pull₂.2 ((hW k x).1 hx).1, ((hW k x).1 hx).2.2⟩
    have l₂ : ∀ k, W k ≤ (M'.pull q).U (fun _ => i) ⊓ L.U k := fun k x hx =>
      ⟨mem_pull.2 ((hW k x).1 hx).2.1, ((hW k x).1 hx).2.2⟩
    obtain ⟨a, ha⟩ : ∃ a : ∀ k, Γ(G, W k)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) (k : L.ι), f y ∈ W k →
        gm f y (W k) (a k) = gw w f y j k * (gw u f y i k)⁻¹ :=
      ⟨fun k => res (l₁ k) (w.s (fun _ => j, k)) * (res (l₂ k) (u.s (fun _ => i, k)))⁻¹, fun Y f y k hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y (l₁ k) hy _)
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y (l₂ k) hy _))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hL x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (hW k x).2 ⟨mem_pull.1 hx.1, hx.2, hk⟩⟩) a (fun k k' x hx => by
        have h₁ := (hW k x).1 hx.1
        have h₂ := (hW k' x).1 hx.2
        rw [ha _ (𝟙 G) x k hx.1, ha _ (𝟙 G) x k' hx.2, hw _ (𝟙 G) x j j k k' h₁.1 h₁.1 h₁.2.2 h₂.2.2,
          hu _ (𝟙 G) x i i k k' h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2, gm_self hM (𝟙 G ≫ q ≫ β) x h₁.1,
          gm_self hM' (𝟙 G ≫ q) x h₁.2.1]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Y f y k hj hi hk => ?_⟩
    have hy := (hW k (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ k) hy s).symm.trans ((congrArg (gm f y (W k)) (hs k)).trans (ha Y f y k hy))
  choose s hs using glue
  exact ⟨s, fun Y f y j i k hj hi hk => by rw [hs j i Y f y k hj hi hk, inv_mul_cancel_right]⟩
end GlobalTheory.IsoDesc
