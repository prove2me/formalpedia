-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.kronecker_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:59.035974+00:00
-- url     : https://prove2.me/submissions/5a6508ab-46bb-45c5-847f-4a5c5e7e77d7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_kronecker

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
theorem _root_.solution (a : ℕ → ℂ) (S : ℂ) (h : Tendsto (recSum a) atTop (𝓝 S)) :
    Tendsto (fun U : ℝ => psum a U / (U : ℂ)) atTop (𝓝 0) := by
  have h1 := (kronecker a S h).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 : Tendsto (fun U : ℝ => (((⌊U⌋₊ : ℝ) / U : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_nat_floor_div_atTop (R := ℝ))
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  have hN : 0 < ⌊U⌋₊ := Nat.floor_pos.2 hU
  have hN' : (⌊U⌋₊ : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Function.comp, psum]
  push_cast
  field_simp
end GlobalTheory.TailIntegralOfSummatory
