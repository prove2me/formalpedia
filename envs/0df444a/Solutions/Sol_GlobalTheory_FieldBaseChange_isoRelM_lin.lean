-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isoRelM_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:30.864086+00:00
-- url     : https://prove2.me/submissions/467c926b-5e8a-4db9-91cb-b318454093c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_iff


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
theorem _root_.solution {S : Type} [CommRing S] {π₁ : Z₁ ⟶ Spec (CommRingCat.of S)}
    {π' : Y' ⟶ Spec (CommRingCat.of S)} (hπ : h₁ ≫ π₁ = π') (c : S)
    {a a' : SecOver π₁ (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b b' : SecOver π' (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a' (m ≫ f₂) (𝟙 _) b') :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (c • a + a' : SecOver π₁ _) (m ≫ f₂) (𝟙 _) (c • b + b' : SecOver π' _) := by
  refine (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).2 fun y i₂ i₁ a₂ a₁ => ?_
  have b₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ :=
    (congrArg (fun q : Y' ⟶ X₁ => q y) h.1 : g₁ (h₁ y) = f₁ (m y)).symm ▸ a₁
  have b₂ : (m ≫ f₂) ((𝟙 Y' ≫ 𝟙 Y') y) ∈ L₂.U i₂ := a₂
  rw [powVal_add _ _ _ y b₁, powVal_add _ _ _ y b₂, powVal_smul _ _ _ y b₁, powVal_smul _ _ _ y b₂,
    (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).1 h _ (𝟙 _) y i₂ i₁ a₂ a₁,
    (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).1 h' _ (𝟙 _) y i₂ i₁ a₂ a₁, Category.assoc, Category.assoc, hπ,
    Category.id_comp π', Category.id_comp π']
  ring
end GlobalTheory.FieldBaseChange
