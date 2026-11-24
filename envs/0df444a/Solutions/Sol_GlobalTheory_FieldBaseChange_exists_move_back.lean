-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.exists_move_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:53:56.754197+00:00
-- url     : https://prove2.me/submissions/cedc1a6c-6449-4971-bdea-331862abd573

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoVal_trans
import Theorems.Thm_GlobalTheory_FieldBaseChange_powVal_trans
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_sec_of_local
import Theorems.Thm_GlobalTheory_FieldBaseChange_gs_isoUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen)
    (m : Y' ⟶ Y) (k : ℤ) {g₂ : Z₂ ⟶ X₂} (h₂ : Y' ⟶ Z₂) (e₂ : h₂ ≫ g₂ = m ≫ f₂) {g₁ : Y' ⟶ X₁} (e₁ : g₁ = m ≫ f₁)
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => k))) :
    ∃ a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b (r ≫ h₂) z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a r z i₁ := by
  subst e₁
  have pt : ∀ y, g₂ (h₂ y) = f₂ (m y) := fun y => congrArg (fun q : Y' ⟶ X₂ => q y) e₂
  have l₁ : ∀ i₁ i₂, LB.wchart L₁ (fun _ : Fin 1 => m ≫ f₁) (fun _ => i₁) ⊓ (m ≫ f₂) ⁻¹ᵁ L₂.U i₂ ≤
      m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)) := fun i₁ i₂ y hy =>
    ⟨mem_pull.2 hy.2, mem_pull.2 (mem_wchart.1 hy.1 0)⟩
  have l₂ : ∀ i₁ i₂, LB.wchart L₁ (fun _ : Fin 1 => m ≫ f₁) (fun _ => i₁) ⊓ (m ≫ f₂) ⁻¹ᵁ L₂.U i₂ ≤
      h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) (fun _ => i₂) := fun i₁ i₂ y hy =>
    (mem_wchart (y := h₂ y)).2 fun _ => (pt y).symm ▸ hy.2
  obtain ⟨a, ha⟩ := exists_sec_of_local (L := L₁) (g := m ≫ f₁) (k := k) (fun i₂ => (m ≫ f₂) ⁻¹ᵁ L₂.U i₂)
    (fun y => exists_chart hL₂ _)
    (fun i₁ i₂ => (res (l₁ i₁ i₂) (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ (-k)).val *
      (Y'.presheaf.map (homOfLE (l₂ i₁ i₂)).op).hom ((h₂.app _).hom (b.f (fun _ => i₂))))
    (fun Z r z i₁ i₂ => (isoVal w (r ≫ m) z i₂ i₁ ^ (-k)).val * powVal b (r ≫ h₂) z i₂)
    (fun Z r z i₁ i₂ a₁ a₂ => by
      have hz : r z ∈ LB.wchart L₁ (fun _ : Fin 1 => m ≫ f₁) (fun _ => i₁) ⊓ (m ≫ f₂) ⁻¹ᵁ L₂.U i₂ :=
        ⟨mem_wchart.2 fun _ => a₁, a₂⟩
      exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_isoUnit w m (-k) i₂ i₁ _ r z hz)
        ((gs_res r z _ hz _).trans (gs_pull r h₂ z _ (l₂ i₁ i₂ hz) _))))
    (fun y i₁ i₂ j₂ a₁ a₂ b₂ => by
      have c₁ : g₂ ((𝟙 Y' ≫ h₂) y) ∈ L₂.U i₂ := (pt y).symm ▸ a₂
      have c₂ : g₂ ((𝟙 Y' ≫ h₂) y) ∈ L₂.U j₂ := (pt y).symm ▸ b₂
      beta_reduce
      rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ b₂ a₁ a₁, powVal_trans b (𝟙 Y' ≫ h₂) y c₁ c₂,
        gm_self hL₁ ((𝟙 Y' ≫ m) ≫ f₁) y a₁, Category.assoc, Category.assoc, e₂, ← mul_assoc, ← Units.val_mul]
      congr 2
      rw [inv_one, mul_one, mul_zpow, zpow_neg, mul_comm, mul_inv_cancel_left])
    (fun y i₁ j₁ i₂ a₁ b₁ a₂ => by
      beta_reduce
      rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ a₂ a₁ b₁, gm_self hL₂ ((𝟙 Y' ≫ m) ≫ f₂) y a₂, one_mul,
        mul_zpow, inv_zpow', neg_neg, Units.val_mul, mul_assoc, Category.assoc])
  refine ⟨a, fun Z r z i₂ i₁ a₂ a₁ => ?_⟩
  rw [ha Z r z i₁ i₂ a₁ a₂, ← mul_assoc, ← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one, one_mul]
end GlobalTheory.FieldBaseChange
