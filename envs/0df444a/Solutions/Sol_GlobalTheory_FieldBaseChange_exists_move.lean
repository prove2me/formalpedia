-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:55.598561+00:00
-- url     : https://prove2.me/submissions/851a9f37-2f6a-45f5-afee-216342f1f739

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
    (m : Y' ⟶ Y) (k : ℤ) {g₁ : Z₁ ⟶ X₁} (h₁ : Y' ⟶ Z₁) (e₁ : h₁ ≫ g₁ = m ≫ f₁) {g₂ : Y' ⟶ X₂} (e₂ : g₂ = m ≫ f₂)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => k))) :
    ∃ b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b r z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a (r ≫ h₁) z i₁ := by
  subst e₂
  have pt : ∀ y, g₁ (h₁ y) = f₁ (m y) := fun y => congrArg (fun q : Y' ⟶ X₁ => q y) e₁
  have l₁ : ∀ i₂ i₁, LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) (fun _ => i₂) ⊓ (m ≫ f₁) ⁻¹ᵁ L₁.U i₁ ≤
      m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)) := fun i₂ i₁ y hy =>
    ⟨mem_pull.2 (mem_wchart.1 hy.1 0), mem_pull.2 hy.2⟩
  have l₂ : ∀ i₂ i₁, LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) (fun _ => i₂) ⊓ (m ≫ f₁) ⁻¹ᵁ L₁.U i₁ ≤
      h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) (fun _ => i₁) := fun i₂ i₁ y hy =>
    (mem_wchart (y := h₁ y)).2 fun _ => (pt y).symm ▸ hy.2
  refine exists_sec_of_local (fun i₁ => (m ≫ f₁) ⁻¹ᵁ L₁.U i₁) (fun y => exists_chart hL₁ _)
    (fun i₂ i₁ => (res (l₁ i₂ i₁) (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ k).val *
      (Y'.presheaf.map (homOfLE (l₂ i₂ i₁)).op).hom ((h₁.app _).hom (a.f (fun _ => i₁))))
    (fun Z r z i₂ i₁ => (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a (r ≫ h₁) z i₁)
    (fun Z r z i₂ i₁ a₂ a₁ => ?_) (fun y i₂ i₁ j₁ a₂ a₁ b₁ => ?_) (fun y i₂ j₂ i₁ a₂ b₂ a₁ => ?_)
  · have hz : r z ∈ LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) (fun _ => i₂) ⊓ (m ≫ f₁) ⁻¹ᵁ L₁.U i₁ :=
      ⟨mem_wchart.2 fun _ => a₂, a₁⟩
    exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_isoUnit w m k i₂ i₁ _ r z hz)
      ((gs_res r z _ hz _).trans (gs_pull r h₁ z _ (l₂ i₂ i₁ hz) _)))
  · have c₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ := (pt y).symm ▸ a₁
    have c₂ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U j₁ := (pt y).symm ▸ b₁
    beta_reduce
    rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ a₂ a₁ b₁, powVal_trans a (𝟙 Y' ≫ h₁) y c₁ c₂,
      gm_self hL₂ ((𝟙 Y' ≫ m) ≫ f₂) y a₂, Category.assoc, Category.assoc, e₁, ← mul_assoc, ← Units.val_mul]
    congr 2
    rw [one_mul, mul_zpow, inv_zpow, mul_comm, mul_inv_cancel_left]
  · beta_reduce
    rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ b₂ a₁ a₁, gm_self hL₁ ((𝟙 Y' ≫ m) ≫ f₁) y a₁, inv_one, mul_one,
      mul_zpow, Units.val_mul, mul_assoc, Category.assoc]
end GlobalTheory.FieldBaseChange
