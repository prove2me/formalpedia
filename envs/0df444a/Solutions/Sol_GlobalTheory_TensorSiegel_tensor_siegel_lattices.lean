-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.tensor_siegel_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:25:40.952433+00:00
-- url     : https://prove2.me/submissions/5e529d10-b5e0-4e33-98bb-51f77c393ba6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_exists_posDef_smul_sub
import Theorems.Thm_GlobalTheory_TensorSiegel_re_hermForm_eq_of_span
import Theorems.Thm_GlobalTheory_TensorSiegel_period_apply
import Theorems.Thm_GlobalTheory_TensorSiegel_eq_period
import Theorems.Thm_GlobalTheory_TensorSiegel_period_isLattice
import Theorems.Thm_GlobalTheory_TensorSiegel_formMatrix_pos
import Theorems.Thm_GlobalTheory_TensorSiegel_formMatrix_isHermitian
import Theorems.Thm_GlobalTheory_TensorSiegel_im_formMatrix_period
import Theorems.Thm_GlobalTheory_TensorSiegel_eq_of_period_equiv
import Theorems.Thm_GlobalTheory_TensorSiegel_endo_period
import Theorems.Thm_GlobalTheory_TensorSiegel_hermForm_endo
import Theorems.Thm_GlobalTheory_TensorSiegel_hermForm_smul_sub
import Theorems.Thm_GlobalTheory_TensorSiegel_bijective_tensor_omegaStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TensorSiegel
namespace GlobalTheory.TensorSiegel
theorem _root_.solution : ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v)) → Function.Bijective EF ∧ (∀ τ : Matrix (Fin h) (Fin h) ℂ, (τ).IsSymm ∧ ((τ).map Complex.im).PosDef → ∃ (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y)) ∧ (∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (Q Q' : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)), (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (∀ x u i, Q' x (σ (u, i)) = (τ').mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q' x = e (Q x)) → τ = τ') ∧ ∀ a : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ∀ (τ : Matrix (Fin h) (Fin h) ℂ) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (fun u => ∑ v, a u v • x v)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro h g G σ EF _ hG hdet hE
  refine ⟨bijective_tensor_omegaStd G (by rw [hdet]; exact isUnit_one) EF hE, ?_, ?_, ?_⟩
  · rintro τ ⟨hs, hτ⟩
    obtain ⟨h1, h2, h3⟩ := period_isLattice σ hτ
    refine ⟨period σ τ, formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ, period_apply σ τ, h1, h2, h3,
      formMatrix_isHermitian σ hG hτ, fun z hz => formMatrix_pos σ hG hτ hz, fun x y => ?_⟩
    rw [im_formMatrix_period σ G hs hτ, hE]
  · rintro τ τ' Q Q' hQ hQ' ⟨e, he⟩
    rw [eq_period σ hQ, eq_period σ hQ'] at he
    exact eq_of_period_equiv σ e he
  · intro a
    have hB : ((a.map (Int.cast : ℤ → ℝ))ᵀ * G.map (Int.cast : ℤ → ℝ) *
        a.map (Int.cast : ℤ → ℝ)).IsHermitian := by
      have := Matrix.isHermitian_conjTranspose_mul_mul (a.map (Int.cast : ℤ → ℝ)) hG.isHermitian
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    obtain ⟨κ₀, hκ₀⟩ := exists_posDef_smul_sub hG hB
    refine ⟨κ₀, fun κ hκ τ Q Hm ⟨hs, hτ⟩ hQ ⟨_, _, h3, _, _, h6⟩ => ?_⟩
    obtain rfl := eq_period σ hQ
    refine ⟨endo σ a, endo_period σ a τ, fun y hy => ?_⟩
    have key := re_hermForm_eq_of_span Hm (formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ) _ h3 (by
      rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      rw [h6, im_formMatrix_period σ G hs hτ, hE])
    have h7 := formMatrix_pos σ (hκ₀ κ hκ) hτ hy
    rw [hermForm_smul_sub] at h7
    rw [key, key, hermForm_endo]
    linarith
end GlobalTheory.TensorSiegel
