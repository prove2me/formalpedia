-- Prove2me | solution 1 for GlobalTheory.PowUnif.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:19.288919+00:00
-- url     : https://prove2.me/submissions/4e08e974-194a-424d-b142-2ea5bc9c8c00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_IsHolFamily_comp
import Theorems.Thm_GlobalTheory_PowUnif_le_wchart_iff
import Theorems.Thm_GlobalTheory_PowUnif_exists_chart
import Theorems.Thm_GlobalTheory_PowUnif_val_g_self
import Theorems.Thm_GlobalTheory_PowUnif_val_iso
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
namespace GlobalTheory.PowUnif
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ Y)}
    (hc : IsHolFamily c) {L : LB X} (hL : L.IsLB) {L' : LB Y} (hL' : L'.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (w : LB.Iso L' (LB.LinComb L φ (fun _ => 1))) (hw : w.IsGen) (fr : K → L.ι → E → ℂ)
    (hhol : ∀ k i, DifferentiableOn ℂ (fr k i) {z | ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ L.U i})
    (hne : ∀ k i z, ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ L.U i → fr k i z ≠ 0)
    (hco : ∀ k i i' z, ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ (L.U i ⊓ L.U i') →
      fr k i z = valAt' (c z ≫ φ k) (L.U i ⊓ L.U i') (L.g i i').val * fr k i' z) :
    ∃ fr' : L'.ι → E → ℂ, (∀ b, DifferentiableOn ℂ (fr' b) {z | ⊤ ≤ c z ⁻¹ᵁ L'.U b}) ∧
      (∀ b z, ⊤ ≤ c z ⁻¹ᵁ L'.U b → fr' b z ≠ 0) ∧
      (∀ b b' z, ⊤ ≤ c z ⁻¹ᵁ (L'.U b ⊓ L'.U b') →
        fr' b z = valAt' (c z) (L'.U b ⊓ L'.U b') (L'.g b b').val * fr' b' z) ∧
      ∀ jj b z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ L'.U b →
        ∏ k, fr k (jj k) z = valAt' (c z) (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val * fr' b z := by
  choose j₀ hj₀ using fun z k => exists_chart hL (c z ≫ φ k)
  have hj : ∀ z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ (j₀ z) := fun z => (le_wchart_iff _ L φ _).2 (hj₀ z)
  let ω : (K → L.ι) → L'.ι → E → ℂ := fun jj b z => valAt' (c z) (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val
  let G : (K → L.ι) → L'.ι → E → ℂ := fun jj b z => (∏ k, fr k (jj k) z) / ω jj b z
  have hω : ∀ jj b z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ L'.U b → ω jj b z ≠ 0 := fun jj b z h₁ h₂ =>
    valAt'_unit_ne_zero (c z) ((top_le_preimage_inf _ _ _).2 ⟨h₁, h₂⟩) (w.s (jj, b))
  have hG : ∀ jj jj' b b' z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj' →
      ⊤ ≤ c z ⁻¹ᵁ L'.U b → ⊤ ≤ c z ⁻¹ᵁ L'.U b' →
      G jj b z = valAt' (c z) (L'.U b ⊓ L'.U b') (L'.g b b').val * G jj' b' z := by
    intro jj jj' b b' z h₁ h₂ h₃ h₄
    have hk : ∀ k, ⊤ ≤ (c z ≫ φ k) ⁻¹ᵁ (L.U (jj k) ⊓ L.U (jj' k)) := fun k => (top_le_preimage_inf _ _ _).2
      ⟨(le_wchart_iff _ L φ _).1 h₁ k, (le_wchart_iff _ L φ _).1 h₂ k⟩
    have e₁ : ω jj b z = _ * _ * ω jj' b' z := val_iso (c z) L L' φ w hw jj jj' b b' h₁ h₂ h₃ h₄
    have e₂ : ∏ k, fr k (jj k) z = (∏ k, valAt' (c z ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) *
        ∏ k, fr k (jj' k) z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => hco k _ _ z (hk k)
    have n₁ : (∏ k, valAt' (c z ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => valAt'_unit_ne_zero _ (hk k) _
    have n₂ := valAt'_unit_ne_zero (c z) ((top_le_preimage_inf _ _ _).2 ⟨h₃, h₄⟩) (L'.g b b')
    have n₃ := hω jj' b' z h₂ h₄
    simp only [G]
    rw [e₁, e₂]
    field_simp
  have hG' : ∀ jj b z, ⊤ ≤ c z ⁻¹ᵁ LB.wchart L φ jj → ⊤ ≤ c z ⁻¹ᵁ L'.U b → G (j₀ z) b z = G jj b z := by
    intro jj b z h₁ h₂
    rw [hG (j₀ z) jj b b z (hj z) h₁ h₂ h₂, val_g_self hL' _ _ h₂, _root_.one_mul]
  refine ⟨fun b z => G (j₀ z) b z, fun b z₀ hz₀ => ?_, fun b z hz => ?_, fun b b' z hz => ?_, fun jj b z h₁ h₂ => ?_⟩
  · have hS := (hc (LB.wchart L φ (j₀ z₀) ⊓ L'.U b) (w.s (j₀ z₀, b)).val)
    have hS₀ := hS.1.mem_nhds ((top_le_preimage_inf _ _ _).2 ⟨hj z₀, hz₀⟩)
    have hd : DifferentiableAt ℂ (G (j₀ z₀) b) z₀ := by
      simp only [G, div_eq_mul_inv]
      classical
      refine DifferentiableAt.mul
        (HasFDerivAt.finsetProd fun k _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
        ((hS.2.differentiableAt hS₀).inv (hω _ _ _ (hj z₀) hz₀))
      exact (hhol k _).differentiableAt (((hc.comp (φ k)) _ 0).1.mem_nhds (hj₀ z₀ k))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hS₀] with z hz
    exact hG' _ _ _ ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  · exact div_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hne k _ z (hj₀ z k)) (hω _ _ _ (hj z) hz)
  · exact hG _ _ _ _ z (hj z) (hj z) ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  · beta_reduce
    rw [hG' jj b z h₁ h₂]
    exact (mul_div_cancel₀ _ (hω jj b z h₁ h₂)).symm
end GlobalTheory.PowUnif
