-- Prove2me | solution 1 for GlobalTheory.PsiTail.pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:13.496438+00:00
-- url     : https://prove2.me/submissions/8ae34955-a0bf-40cc-80ad-6239824223b1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.PsiTail
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory.PsiTail
theorem _root_.solution (b : ℝ) (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ n ≤ (n.factorial / b ^ n) * Real.exp (b * x) := by
  have h := Real.pow_div_factorial_le_exp (b * x) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h]
end GlobalTheory.PsiTail
