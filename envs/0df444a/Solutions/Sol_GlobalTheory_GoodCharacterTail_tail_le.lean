-- Prove2me | solution 1 for GlobalTheory.GoodCharacterTail.tail_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:52.443867+00:00
-- url     : https://prove2.me/submissions/139376a3-9211-4123-a7b8-132981ac8735

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2IntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TailAndSumBound
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_tail_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open GlobalTheory GlobalTheory.GoodCharacterTail
open Formalism.HermitianLattices.GL2PrimeSums
namespace GlobalTheory.GoodCharacterTail
theorem _root_.solution (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (Z B : ℝ) (hZ : 1 ≤ Z)
    (hB : ∀ U : ℝ, Z ≤ U → ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤ B) :
    ‖S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)‖ ≤ B := by
  obtain ⟨I, hI, hG⟩ := GlobalTheory.TailIntegralOfSummatory.tail_integral a S hS Z hZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have h1 : Gchi a S Z = Z * (∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)) - psum a Z - Z * S := by
    unfold Gchi psum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have h2 : S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ) = I - psum a Z / Z := by
    rw [h1] at hG
    field_simp
    linear_combination -hG
  have h3 : ‖I‖ ≤ B - ‖psum a Z‖ / Z := by
    refine le_of_tendsto hI.norm ?_
    filter_upwards [eventually_ge_atTop Z] with U hU
    have h4 := intervalIntegral.norm_integral_le_integral_norm
      (f := fun u : ℝ => psum a u / (u : ℂ) ^ 2) (μ := MeasureTheory.volume) hU
    have h5 : (fun u : ℝ => ‖psum a u / (u : ℂ) ^ 2‖) = fun u : ℝ => ‖psum a u‖ / u ^ 2 := by
      funext u
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h5] at h4
    have := hB U hU
    linarith
  rw [h2]
  have h6 := norm_sub_le I (psum a Z / Z)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ0] at h6
  linarith
end GlobalTheory.GoodCharacterTail
