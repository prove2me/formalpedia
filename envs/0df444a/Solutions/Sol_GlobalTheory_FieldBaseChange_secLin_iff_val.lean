-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.secLin_iff_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:20.371665+00:00
-- url     : https://prove2.me/submissions/8788d230-5d45-4666-8ce9-96bd0ccd233d

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
    {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c ↔ ∀ y J, Good L y J →
      sval s₁ (𝟙 Y') y J = ∑ i, gs (𝟙 Y') y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ h) y J := by
  have key : ∀ (y : Y') (j₁ : K' → L.ι) (j₂ : K → L.ι)
      (hm : y ∈ LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂)
      (a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ j₂),
      gs (𝟙 Y') y _ (∑ i, resTop _ (c i) * (Y'.presheaf.map (homOfLE a₂).op).hom
        ((h.app (LB.wchart L φ j₂)).hom ((s i).f j₂))) =
        ∑ i, gs (𝟙 Y') y ⊤ (c i) * gs (𝟙 Y' ≫ h) y (LB.wchart L φ j₂) ((s i).f j₂) := fun y j₁ j₂ hm a₂ => by
    refine ((gs_eq _ y _ hm _).trans (by rw [map_sum, map_sum])).trans (Finset.sum_congr rfl fun i _ =>
      (gs_eq _ y _ hm _).symm.trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hm _)
        ((gs_res _ y a₂ hm _).trans (gs_pull _ h y _ (a₂ hm) _)))))
  constructor
  · intro H y J hJ
    simp only [sval_of (s _) (𝟙 Y' ≫ h) y J (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ₁ (fun k => J (𝟙 Y' ≫ φ₁ k)) ⊓
        LB.wchart L (fun k => h ≫ φ k) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) :=
      ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
    have e := H (fun k => J (𝟙 Y' ≫ φ₁ k)) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (𝟙 Y' ≫ q)) e)
    exact (gs_res _ y _ hm _).symm.trans ((congrArg (gs (𝟙 Y') y _) e).trans (key y _ _ hm _))
  · intro H j₁ j₂ hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
      rintro (a | a)
      exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have := H y J hJ
    rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k))] at this
    simp only [sval_of (s _) (𝟙 Y' ≫ h) y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
    exact (gs_res _ y _ hy _).trans (this.trans (key y _ _ hy _).symm)
end GlobalTheory.FieldBaseChange
