-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isoRelM_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:31:44.464828+00:00
-- url     : https://prove2.me/submissions/e5de3184-a417-443a-87da-49c78950a9aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_powVal_ext
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_move
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_move_back
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
  {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hw : w.IsGen) (e₁ : h₁ ≫ g₁ = m ≫ f₁) (n : Z₁ ⟶ Y')
    (hn : n ≫ h₁ = 𝟙 _) (hn' : h₁ ≫ n = 𝟙 _) :
    (∀ a, ∃! b, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b) ∧
      ∀ b, ∃! a, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b := by
  have e₂ : 𝟙 Y' ≫ m ≫ f₂ = m ≫ f₂ := Category.id_comp _
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← e₁, ← Category.assoc, hn, Category.id_comp]
  refine ⟨fun a => existsUnique_of_exists_of_unique ?_ fun b b' h h' => ?_,
    fun b => existsUnique_of_exists_of_unique ?_ fun a a' h h' => ?_⟩
  · obtain ⟨b, hb⟩ := exists_move hL₁ hL₂ hw m k h₁ e₁ rfl a
    exact ⟨b, (isoRelM_iff w m k h₁ e₁ _ e₂ a b).2 fun y i₂ i₁ a₂ a₁ => by
      rw [Category.comp_id]; exact hb _ _ y i₂ i₁ a₂ a₁⟩
  · refine powVal_ext hL₂ fun y i hi => ?_
    obtain ⟨i₁, a₁⟩ := exists_chart hL₁ (f₁ (m y))
    have := ((isoRelM_iff w m k h₁ e₁ _ e₂ a b).1 h _ (𝟙 _) y i i₁ hi a₁).trans
      ((isoRelM_iff w m k h₁ e₁ _ e₂ a b').1 h' _ (𝟙 _) y i i₁ hi a₁).symm
    rwa [Category.comp_id] at this
  · obtain ⟨a, ha⟩ := exists_move_back hL₁ hL₂ hw (n ≫ m) k n (Category.assoc _ _ _).symm e₃ b
    refine ⟨a, (isoRelM_iff w m k h₁ e₁ _ e₂ a b).2 fun y i₂ i₁ a₂ a₁ => ?_⟩
    have e : h₁ ≫ n ≫ m = m := by rw [← Category.assoc, hn', Category.id_comp]
    have pt : (n ≫ m) (h₁ y) = m y := congrArg (fun q : Y' ⟶ Y => q y) e
    have := ha _ h₁ y i₂ i₁ (pt.symm ▸ a₂) (pt.symm ▸ a₁)
    rw [hn', e] at this
    simpa only [Category.id_comp] using this
  · refine powVal_ext hL₁ fun y i hi => ?_
    obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
    have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
    have := ((isoRelM_iff w m k h₁ e₁ _ e₂ a b).1 h _ n y i₂ i a₂ a₁).symm.trans
      ((isoRelM_iff w m k h₁ e₁ _ e₂ a' b).1 h' _ n y i₂ i a₂ a₁)
    rw [hn] at this
    exact (Units.mul_right_inj _).1 this
end GlobalTheory.FieldBaseChange
