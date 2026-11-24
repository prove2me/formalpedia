-- Prove2me | solution 1 for GlobalTheory.MulSplit.Descends.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:24.510157+00:00
-- url     : https://prove2.me/submissions/3812573e-1ec3-4402-9173-1ff0a9c0fc8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_gs_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}
namespace GlobalTheory.MulSplit
namespace Descends
theorem _root_.solution {A : Scheme.{0}} {q : A ⟶ A} {τ : G → (A ⟶ A)} (H : Descends q τ)
    (hτq : ∀ g, τ g ≫ q = q) (e : Y ≅ A)
    {q' : Y ⟶ Y} {τ' : G → (Y ⟶ Y)} (hq : e.inv ≫ q' = q ≫ e.inv) (hτ : ∀ g, e.inv ≫ τ' g = τ g ≫ e.inv) :
    Descends q' τ' := by
  obtain rfl : q' = e.hom ≫ q ≫ e.inv := by rw [← hq, Iso.hom_inv_id_assoc]
  refine ⟨fun U => ?_, fun U f hf => ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso (e.hom.app (q ⁻¹ᵁ (e.inv ⁻¹ᵁ U)))).1.comp
      ((H.1 (e.inv ⁻¹ᵁ U)).comp (ConcreteCategory.bijective_of_isIso (e.inv.app U)).1)
  · have m : q ⁻¹ᵁ (e.inv ⁻¹ᵁ U) ≤ e.inv ⁻¹ᵁ ((e.hom ≫ q ≫ e.inv) ⁻¹ᵁ U) := fun z hz =>
      (congrArg (fun t => t z ∈ U) hq).mpr hz
    obtain ⟨a, ha⟩ := H.2 (e.inv ⁻¹ᵁ U) ((e.inv.appLE _ _ m).hom f) (fun g z hz => by
      have hz' : τ g z ∈ q ⁻¹ᵁ (e.inv ⁻¹ᵁ U) := (congrArg (fun t => e.inv (t z) ∈ U) (hτq g)).mpr hz
      have hz'' : τ' g (e.inv z) ∈ (e.hom ≫ q ≫ e.inv) ⁻¹ᵁ U :=
        (congrArg (fun t => t z ∈ (e.hom ≫ q ≫ e.inv) ⁻¹ᵁ U) (hτ g)).mpr (m hz')
      rw [gs_appLE _ _ _ m (τ g) z hz', gs_appLE _ _ _ m (𝟙 A) z hz, ← hτ, gs_comp _ _ _ _ hz'', hf g _ (m hz),
        ← gs_comp e.inv (𝟙 Y) z _ (m hz), Category.comp_id, Category.id_comp])
    have m' : U ≤ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U) := fun y hy => (congrArg (fun t => t y ∈ U) e.hom_inv_id).mpr hy
    refine ⟨(e.hom.appLE _ _ m').hom a, fn_ext fun y hy => ?_⟩
    have hy' : e.hom y ∈ q ⁻¹ᵁ (e.inv ⁻¹ᵁ U) := hy
    rw [gs_pull (𝟙 Y) _ y U hy, Category.id_comp, gs_appLE _ _ _ m' _ y hy, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, ← gs_pull e.hom q y _ hy', ha, gs_appLE _ _ _ m _ y hy', Iso.hom_inv_id]
end Descends
end GlobalTheory.MulSplit
