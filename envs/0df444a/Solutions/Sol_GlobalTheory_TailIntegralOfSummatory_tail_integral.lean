-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.tail_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:50.200245+00:00
-- url     : https://prove2.me/submissions/9c5a0ef5-0954-4d41-bc00-13468a7d2c61

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_kronecker_real
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_integral_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.TailIntegralOfSummatory
namespace GlobalTheory.TailIntegralOfSummatory
theorem _root_.solution : Formalism.HermitianLattices.GL2PrimeSums.SmoothedRemainderIntegralFormula := by
  intro a S h y hy
  have h' : Tendsto (recSum a) atTop (𝓝 S) := h
  refine ⟨(S - 0) - (recSum a ⌊y⌋₊ - psum a y / y), ?_, ?_⟩
  · have h1 := ((h'.comp (tendsto_nat_floor_atTop (α := ℝ))).sub
      (kronecker_real a S h')).sub_const (recSum a ⌊y⌋₊ - psum a y / y)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    rw [integral_eq a hy hU]
    rfl
  · have hy0 : (y : ℂ) ≠ 0 := by
      have : y ≠ 0 := by linarith
      exact_mod_cast this
    have e : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)
        = y * recSum a ⌊y⌋₊ - psum a y := by
      unfold recSum psum
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    unfold Gchi
    rw [e]
    field_simp
    ring
end GlobalTheory.TailIntegralOfSummatory
