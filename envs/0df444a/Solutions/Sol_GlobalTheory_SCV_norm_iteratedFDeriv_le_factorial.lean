-- Prove2me | solution 1 for GlobalTheory.SCV.norm_iteratedFDeriv_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:32:31.021924+00:00
-- url     : https://prove2.me/submissions/4a253cb0-746f-4c18-bf7e-72769c125b12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_norm_iteratedFDeriv_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} {R M : ℝ} (hR : 0 < R) (hc : closedBall c R ⊆ U)
    (hM : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ n ! * (M * (2 * Real.exp 1 / R) ^ n) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self hR.le))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hM c (mem_closedBall_self hR.le)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) * (R / n) = R := by field_simp
  have h1 := norm_iteratedFDeriv_le_pow hU hf (δ := R / n) (M := M) (by positivity) n c
    (by rwa [e]) (by rwa [e])
  have h2 := Real.pow_div_factorial_le_exp (n : ℝ) hn'.le n
  rw [div_le_iff₀ (by positivity), ← Real.exp_one_pow] at h2
  refine h1.trans ?_
  calc M * (2 / (R / n)) ^ n = (M * (2 / R) ^ n) * (n : ℝ) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ (M * (2 / R) ^ n) * (Real.exp 1 ^ n * n !) := by gcongr
    _ = n ! * (M * (2 * Real.exp 1 / R) ^ n) := by
        rw [show 2 * Real.exp 1 / R = 2 / R * Real.exp 1 by ring, mul_pow]
        ring
end GlobalTheory.SCV
