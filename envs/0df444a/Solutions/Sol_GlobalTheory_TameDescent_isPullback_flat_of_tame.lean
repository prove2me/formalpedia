-- Prove2me | solution 1 for GlobalTheory.TameDescent.isPullback_flat_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:47.400608+00:00
-- url     : https://prove2.me/submissions/0f4fd0f9-b624-4d77-901a-0e3dc244cd6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPullbackFlatOfTame
import Theorems.Thm_GlobalTheory_TameDescent_isPullback_of_isPushout_app
import Theorems.Thm_GlobalTheory_TameDescent_isPushout_and_flat
import Theorems.Thm_GlobalTheory_T_quotient_isFinite_and_descends_finiteness_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameDescent
namespace GlobalTheory.TameDescent
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst p x ≫ (τ g).hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  intro Γ _ _ X X' Y Y' _ ρ τ π φ p p' hπ hφ w hp _ _ _ htame hfix
  obtain ⟨_, _, -⟩ := GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ Y Y' τ φ hφ X' p' (by rw [w]; infer_instance)
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p'
  have H := isPushout_and_flat ρ τ π φ p p' hπ.2.1 hπ.2.2 hφ.2.1 hφ.2.2 w hp htame hfix
  refine ⟨isPullback_of_isPushout_app π φ p p' w fun V W hV hW e e' => (H V W hV hW e e').1,
    ⟨fun {V} hV {W} hW e => (H V W hV hW e ?_).2⟩, inferInstance⟩
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact φ.preimage_mono e
end GlobalTheory.TameDescent
