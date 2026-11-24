-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.growth_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:08:40.924305+00:00
-- url     : https://prove2.me/submissions/2a3dd39a-7bc8-4ca2-9bb4-c90ce2724504

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Theorems.Thm_GlobalTheory_ZetaLeft_norm_sub_one_mul_riemannZeta_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution : ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (z : ℂ), -(7 / 4 : ℝ) ≤ z.re →
    ‖LFunctionTrivChar₁ q z‖ ≤ B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 := by
  obtain ⟨B, hB, G⟩ := ZetaLeft.norm_sub_one_mul_riemannZeta_le
  refine ⟨B + 1, by positivity, fun q _ z hz => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hP : ∀ s : ℂ, -(7 / 4 : ℝ) ≤ s.re →
      ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (q : ℝ) ^ 5 := by
    intro s hs
    rw [norm_prod]
    calc _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) ^ 3 := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
          have hp' := Nat.prime_of_mem_primeFactors hp
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, Complex.norm_natCast_cpow_of_pos hp'.pos]
          have : (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ ((2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [neg_re]; push_cast; linarith)
          rw [Real.rpow_natCast] at this
          nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (p : ℝ))]
      _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ 3 := by rw [Finset.prod_pow, Nat.cast_prod]
      _ ≤ (q : ℝ) ^ 3 := by
          gcongr
          exact Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
      _ ≤ _ := pow_le_pow_right₀ hq (by norm_num)
  have h5 : (1 : ℝ) ≤ (‖z‖ + 2) ^ 5 := one_le_pow₀ (by linarith [norm_nonneg z])
  have hq5 : (0 : ℝ) ≤ (q : ℝ) ^ 5 := by positivity
  by_cases h1 : z = 1
  · have := hP 1 (by norm_num)
    simp only [cpow_neg_one] at this
    have e : LFunctionTrivChar₁ q z = ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) := by
      rw [h1, LFunctionTrivChar₁, Function.update_self]
    rw [e]
    refine this.trans ?_
    calc (q : ℝ) ^ 5 = 1 * (q : ℝ) ^ 5 * 1 := by ring
      _ ≤ _ := by gcongr; linarith
  · rw [LFunctionTrivChar₁, Function.update_of_ne h1, LFunctionTrivChar_eq_mul_riemannZeta h1,
      mul_left_comm, norm_mul]
    calc _ ≤ (q : ℝ) ^ 5 * (B * (‖z‖ + 2) ^ 5) :=
          mul_le_mul (hP z hz) (G z hz h1) (norm_nonneg _) hq5
      _ = B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 := by ring
      _ ≤ _ := by gcongr; linarith
end GlobalTheory.LogDerivHigher
