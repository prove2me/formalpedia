-- Prove2me | solution 1 for GlobalTheory.Hk.LamRay.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:45.453556+00:00
-- url     : https://prove2.me/submissions/5b1d085f-c65f-44fb-9c86-a0f49c630926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
import Theorems.Thm_GlobalTheory_QuadraticZeta_norm_eq_sq
import Theorems.Thm_GlobalTheory_discr_eq_neg_of_sq_eq
import Theorems.Thm_GlobalTheory_ringOfIntegers_sqrt_neg_three_mod_four


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]
open QuadraticZeta
namespace GlobalTheory.Hk.LamRay
theorem _root_.solution {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) : ∃ ω : 𝓞 K, (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  have hsq : Squarefree d := hp.squarefree
  have hD := discr_eq_neg_of_sq_eq h2 hsq hd hr
  obtain ⟨w, bar, hw, -, hgen, hσ, σ, hσr⟩ :=
    ringOfIntegers_sqrt_neg_three_mod_four d hsq hd K h2 r hr
  refine ⟨w, hgen, fun a b => ?_⟩
  have h1 := norm_eq_sq h2 hD σ (((a : 𝓞 K) + b * w : 𝓞 K) : K)
  rw [← Algebra.coe_norm_int] at h1
  have h3 : σ (w : K) = (1 + Complex.I * √d) / 2 := by
    have := congrArg σ hw
    rw [map_mul, map_add, map_one, map_ofNat, hσr] at this
    linear_combination this / 2
  have h4 : σ (((a : 𝓞 K) + b * w : 𝓞 K) : K)
      = ((a + b / 2 : ℝ) : ℂ) + ((b * √d / 2 : ℝ) : ℂ) * Complex.I := by
    have h7 : (((a : 𝓞 K) + b * w : 𝓞 K) : K) = a + b * (w : K) := by simp
    rw [h7, map_add, map_mul, map_intCast, map_intCast, h3]
    push_cast
    ring
  rw [h4, Complex.sq_norm, Complex.normSq_add_mul_I] at h1
  have h5 : √(d : ℝ) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have h6 : ((Algebra.norm ℤ ((a : 𝓞 K) + b * w) : ℤ) : ℝ) * 4
      = (2 * a + b) ^ 2 + d * b ^ 2 := by
    push_cast at h1
    rw [h1]
    linear_combination (b : ℝ) ^ 2 * h5
  exact_mod_cast h6
end GlobalTheory.Hk.LamRay
