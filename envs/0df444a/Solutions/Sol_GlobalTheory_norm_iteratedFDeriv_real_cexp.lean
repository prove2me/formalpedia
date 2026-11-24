-- Prove2me | solution 1 for GlobalTheory.norm_iteratedFDeriv_real_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:18.560437+00:00
-- url     : https://prove2.me/submissions/8d8e397e-479f-488a-9ea4-b53536cd509a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivCexpPhaseLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open scoped Nat
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]
end GlobalTheory
