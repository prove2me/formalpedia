-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.secScal_iff_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.453801+00:00
-- url     : https://prove2.me/submissions/1c23f1b1-bd85-4e12-a2a2-1c45e9cb88ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
variable {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'} {p : Y' ⟶ Y}
  (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hL : L.IsLB) {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Γ(Y', ⊤)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ ε s h c ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J := by
  have key : ∀ (y : Y') (j₁ : K' → L.ι) (j₂ : K → L.ι)
      (hm : y ∈ LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂)
      (a₁ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ≤ LB.wchart L φ₁ j₁)
      (a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ j₂),
      gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE a₂).op).hom ((h.app (LB.wchart L φ j₂)).hom (s.f j₂))) =
        gs (𝟙 Y' ≫ h) y (LB.wchart L φ j₂) (s.f j₂) ∧
      gs (𝟙 Y') y _ (resTop _ c * (Y'.presheaf.map (homOfLE a₁).op).hom (s₁.f j₁)) =
        gs (𝟙 Y') y ⊤ c * gs (𝟙 Y') y (LB.wchart L φ₁ j₁) (s₁.f j₁) := fun y j₁ j₂ hm a₁ a₂ =>
    ⟨(gs_res _ y a₂ hm _).trans (gs_pull _ h y _ (a₂ hm) _),
      (gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hm _) (gs_res _ y a₁ hm _))⟩
  constructor
  · intro H y J hJ
    rw [sval_of s (𝟙 Y' ≫ h) y J (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ₁ (fun k => J (𝟙 Y' ≫ φ₁ k)) ⊓
        LB.wchart L (fun k => h ≫ φ k) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) :=
      ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
    have e := H (fun k => J (𝟙 Y' ≫ φ₁ k)) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (𝟙 Y' ≫ q)) e)
    obtain ⟨k₁, k₂⟩ := key y _ _ hm _ _
    exact k₁.symm.trans ((congrArg (gs (𝟙 Y') y _) e).trans k₂)
  · intro H j₁ j₂ hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
      rintro (a | a)
      exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have := H y J hJ
    rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
      sval_of s _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
    obtain ⟨k₁, k₂⟩ := key y _ _ hy _ _
    exact k₁.trans (this.trans k₂.symm)
end GlobalTheory.FieldBaseChange
