-- Prove2me | solution 1 for GlobalTheory.norm_map_eq_sqrt_of_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:23.6649+00:00
-- url     : https://prove2.me/submissions/a29d0f05-05c4-4991-b4f8-c5c1b38fdd4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LogNormMapPowMulPowOfMulConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) : ‖σ x‖ = (g : ℝ) ^ (1 / 2 : ℝ) := by
  have h : σ x * starRingEnd ℂ (σ x) = (g : ℂ) := by
    rw [← hy, ← map_mul, hxy, map_natCast]
  have h2 : ((‖σ x‖ : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.mul_conj', h]
  have h3 : ‖σ x‖ ^ 2 = (g : ℝ) := by exact_mod_cast h2
  rw [← Real.sqrt_eq_rpow, ← h3, Real.sqrt_sq (norm_nonneg _)]
end GlobalTheory
