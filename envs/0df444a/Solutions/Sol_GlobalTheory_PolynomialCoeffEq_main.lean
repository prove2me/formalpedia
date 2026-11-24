-- Prove2me | solution 1 for GlobalTheory.PolynomialCoeffEq.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:42:17.918331+00:00
-- url     : https://prove2.me/submissions/5d335af4-9e14-4425-940c-b7dc3c88d8ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_Imports
import Theorems.Thm_GlobalTheory_PolynomialCoeffEq_coeff_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialCoeffEq
open Module
namespace GlobalTheory.PolynomialCoeffEq
theorem _root_.solution : ∀ {R : Type} [inst : AddCommGroup R] [inst_1 : Module ℝ R] [FiniteDimensional ℝ R] (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ (u v : R), ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) v = ((g : R → R →ₗ[ℝ] ℝ) v : R → ℝ) u) → (∀ (u : R), u ≠ (0 : R) → (0 : ℝ) < ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) u) → ∃ (n : ℕ) (e : Fin n → R), ∀ (x : R), ∑ k : Fin n, ((g : R → R →ₗ[ℝ] ℝ) x : R → ℝ) (e k) • e k = x := by
  intro R _ _ _ g hsym hpos
  have h2 : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g) ⟨hsym⟩
  have hv' : ∀ i j, i ≠ j → g (v i) (v j) = 0 := LinearMap.BilinForm.iIsOrtho_def.mp hv
  have hpos' : ∀ k, 0 < g (v k) (v k) := fun k => hpos _ (v.ne_zero k)
  refine ⟨_, fun k => (Real.sqrt (g (v k) (v k)))⁻¹ • v k, fun x => ?_⟩
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, coeff_eq g v hv' x k, smul_smul]
  congr 1
  have hs := Real.mul_self_sqrt (hpos' k).le
  have he : (Real.sqrt (g (v k) (v k)))⁻¹ * (v.repr x k * g (v k) (v k)) *
      (Real.sqrt (g (v k) (v k)))⁻¹ =
      v.repr x k * (g (v k) (v k) * (Real.sqrt (g (v k) (v k)) * Real.sqrt (g (v k) (v k)))⁻¹) := by
    ring
  rw [he, hs, mul_inv_cancel₀ (hpos' k).ne', mul_one]
end GlobalTheory.PolynomialCoeffEq
