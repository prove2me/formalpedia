-- Prove2me | solution 1 for GlobalTheory.PolynomialCoeffEq.coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:16.190959+00:00
-- url     : https://prove2.me/submissions/61941dee-909a-401c-9150-5ebd476c1af8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_Imports

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
theorem _root_.solution {R : Type} [AddCommGroup R] [Module ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) {n : ℕ} (v : Basis (Fin n) ℝ R)
    (hv : ∀ i j, i ≠ j → g (v i) (v j) = 0) (x : R) (k : Fin n) :
    g x (v k) = v.repr x k * g (v k) (v k) := by
  conv_lhs => rw [← v.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · intro i _ hik
    rw [hv i k hik, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h
end GlobalTheory.PolynomialCoeffEq
