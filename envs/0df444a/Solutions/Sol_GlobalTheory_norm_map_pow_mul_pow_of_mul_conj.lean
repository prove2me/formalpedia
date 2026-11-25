-- Prove2me | solution 1 for GlobalTheory.norm_map_pow_mul_pow_of_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:44.992624+00:00
-- url     : https://prove2.me/submissions/870a8cfa-28c6-4d94-b609-8bdac9874da6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LogNormMapPowMulPowOfMulConj
import Theorems.Thm_GlobalTheory_norm_map_eq_sqrt_of_mul_conj

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
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) (a b : ℕ) :
    ‖σ (x ^ a * y ^ b)‖ = (g : ℝ) ^ (((a : ℝ) + b) / 2) := by
  have h1 := norm_map_eq_sqrt_of_mul_conj σ x y g hxy hy
  have hyn : ‖σ y‖ = ‖σ x‖ := by rw [hy]; simp
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow, hyn, ← pow_add, h1,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg g)]
  congr 1
  push_cast
  ring
end GlobalTheory
