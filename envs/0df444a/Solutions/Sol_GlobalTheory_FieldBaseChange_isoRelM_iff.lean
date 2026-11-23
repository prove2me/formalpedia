-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isoRelM_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:48.667512+00:00
-- url     : https://prove2.me/submissions/eb58c138-2d73-46ab-b660-9bf220c16ba5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Theorems.Thm_GlobalTheory_FieldBaseChange_gs_isoUnit
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
theorem _root_.solution (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y) (k : ℕ) {g₁ : Z₁ ⟶ X₁} (h₁ : Y' ⟶ Z₁)
    (e₁ : h₁ ≫ g₁ = m ≫ f₁) {g₂ : Z₂ ⟶ X₂} (h₂ : Y' ⟶ Z₂) (e₂ : h₂ ≫ g₂ = m ≫ f₂)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))) :
    (GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b (r ≫ h₂) z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ (k : ℤ)).val * powVal a (r ≫ h₁) z i₁) ∧
    ((∀ (y : Y') i₂ i₁, f₂ (m y) ∈ L₂.U i₂ → f₁ (m y) ∈ L₁.U i₁ →
        powVal b (𝟙 Y' ≫ h₂) y i₂ = (isoVal w (𝟙 Y' ≫ m) y i₂ i₁ ^ (k : ℤ)).val * powVal a (𝟙 Y' ≫ h₁) y i₁) →
      GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁ (O : Y'.Opens) (_ : r z ∈ O)
      (a₀ : O ≤ m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)))
      (a₁ : O ≤ h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) (fun _ => i₁))
      (a₂ : O ≤ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) (fun _ => i₂)),
      gs r z O ((Y'.presheaf.map (homOfLE a₂).op).hom ((h₂.app _).hom (b.f (fun _ => i₂)))) =
        powVal b (r ≫ h₂) z i₂ ∧
      gs r z O ((res a₀ (pullU m _ (w.s (fun _ => i₂, fun _ => i₁)))).val ^ k *
        (Y'.presheaf.map (homOfLE a₁).op).hom ((h₁.app _).hom (a.f (fun _ => i₁)))) =
        (isoVal w (r ≫ m) z i₂ i₁ ^ (k : ℤ)).val * powVal a (r ≫ h₁) z i₁ := fun Z r z i₂ i₁ O hz a₀ a₁ a₂ =>
    ⟨(gs_res r z a₂ hz _).trans (gs_pull r h₂ z _ (a₂ hz) _), (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
      ((congrArg (gs r z O) (by rw [zpow_natCast, Units.val_pow_eq_pow_val])).trans
        (gs_isoUnit w m k i₂ i₁ a₀ r z hz)) ((gs_res r z a₁ hz _).trans (gs_pull r h₁ z _ (a₁ hz) _)))⟩
  have pt₁ : ∀ y, g₁ (h₁ y) = f₁ (m y) := fun y => congrArg (fun q : Y' ⟶ X₁ => q y) e₁
  have pt₂ : ∀ y, g₂ (h₂ y) = f₂ (m y) := fun y => congrArg (fun q : Y' ⟶ X₂ => q y) e₂
  constructor
  · intro H Z r z i₂ i₁ a₂ a₁
    have hz : r z ∈ GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => i₂, fun _ => i₁) (fun _ => i₁) (fun _ => i₂) :=
      ⟨⟨⟨mem_pull.2 a₂, mem_pull.2 a₁⟩, (mem_wchart (y := h₁ (r z))).2 fun _ => (pt₁ _).symm ▸ a₁⟩,
        (mem_wchart (y := h₂ (r z))).2 fun _ => (pt₂ _).symm ▸ a₂⟩
    obtain ⟨k₁, k₂⟩ := key Z r z i₂ i₁ _ hz (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      inf_le_right
    exact k₁.symm.trans ((congrArg (gs r z _) (H.2.2 (fun _ => i₂, fun _ => i₁) (fun _ => i₁) (fun _ => i₂)
      rfl rfl)).trans k₂)
  · intro H
    refine ⟨e₁, e₂, ?_⟩
    rintro ⟨p₁, p₂⟩ j₁ j₂ c₁ c₂
    obtain rfl : j₁ = fun _ => p₂ PUnit.unit := funext fun i => (congrArg j₁ (Subsingleton.elim i 0)).trans c₁
    obtain rfl : j₂ = fun _ => p₁ PUnit.unit := funext fun i => (congrArg j₂ (Subsingleton.elim i 0)).trans c₂
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := key _ (𝟙 Y') y (p₁ PUnit.unit) (p₂ PUnit.unit) _ hy (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right
    exact k₁.trans ((H y _ _ (mem_pull.1 hy.1.1.1) (mem_pull.1 hy.1.1.2)).trans k₂.symm)
end GlobalTheory.FieldBaseChange
