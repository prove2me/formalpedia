-- Prove2me | solution 1 for GlobalTheory.AbCoh.Bock_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:32:34.762319+00:00
-- url     : https://prove2.me/submissions/a71c3df5-b15f-40e2-82b3-b7baa3ecd8f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftingObstructionBocksteinAdd
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add, hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add]
  · rw [map_add, hcx, hcx', map_add]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add]
  · rw [map_add, hez, hez', map_add]
end GlobalTheory.AbCoh
