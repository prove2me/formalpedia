-- Prove2me | solution 1 for GlobalTheory.RiemannRel.exists_siegel_of_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:45.235147+00:00
-- url     : https://prove2.me/submissions/d4595d86-a686-4144-929e-f067d01f5869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelPeriodOfSymplecticBasis
import Theorems.Thm_GlobalTheory_RiemannRel_hermForm_cols
import Theorems.Thm_GlobalTheory_RiemannRel_matrix_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix
open GlobalTheory GlobalTheory.RiemannRel
namespace GlobalTheory.RiemannRel
theorem _root_.solution : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  intro h Hm v hH hpos hv
  let L : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inl i) k
  let M : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inr i) k
  obtain ⟨hM, hs, hp⟩ := matrix_form Hm L M hH hpos
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inr i) (.inr j)).trans ?_
      simp [omegaStd])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inr j)).trans ?_
      simp [omegaStd, Pi.single_apply, Matrix.one_apply, eq_comm])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inl j)).trans ?_
      simp [omegaStd])
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hM
  refine ⟨M⁻¹ * L, M.toLinearEquiv' inferInstance, hs, hp, fun a => ?_⟩
  change M.mulVec (per (M⁻¹ * L) a) = _
  rw [per, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hM]
  funext k
  simp [L, M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
end GlobalTheory.RiemannRel
